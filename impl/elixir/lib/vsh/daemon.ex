# SPDX-License-Identifier: AGPL-3.0-or-later

defmodule VSH.Daemon do
  @moduledoc """
  Valence Shell Daemon - Unix Socket Server

  Listens on a Unix socket for commands from:
  - Rust CLI (vsh)
  - ReScript MCP server
  - Other clients

  ## Protocol

  JSON-RPC 2.0 over Unix socket with methods:
  - `mkdir`, `rmdir`, `touch`, `rm` - Filesystem operations
  - `undo`, `redo` - Reversibility
  - `history`, `status` - Introspection
  - `begin`, `commit`, `rollback` - Transactions
  - `proofs` - Verification info
  """

  use GenServer
  require Logger

  @socket_path "/tmp/vsh-daemon.sock"

  ## Client API

  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts, name: __MODULE__)
  end

  def socket_path, do: @socket_path

  ## Server Callbacks

  @impl true
  def init(opts) do
    socket_path = Keyword.get(opts, :socket_path, @socket_path)

    # Remove existing socket
    File.rm(socket_path)

    case :gen_tcp.listen(0, [
      {:ifaddr, {:local, socket_path}},
      :binary,
      packet: :line,
      active: false,
      reuseaddr: true
    ]) do
      {:ok, listen_socket} ->
        Logger.info("VSH Daemon listening on #{socket_path}")
        Task.start_link(fn -> accept_loop(listen_socket) end)
        {:ok, %{socket: listen_socket, path: socket_path}}

      {:error, reason} ->
        Logger.error("Failed to start daemon: #{inspect(reason)}")
        {:stop, reason}
    end
  end

  @impl true
  def terminate(_reason, state) do
    File.rm(state.path)
    :ok
  end

  ## Socket Handling

  defp accept_loop(listen_socket) do
    case :gen_tcp.accept(listen_socket) do
      {:ok, client} ->
        Task.start_link(fn -> handle_client(client) end)
        accept_loop(listen_socket)

      {:error, :closed} ->
        :ok

      {:error, reason} ->
        Logger.error("Accept error: #{inspect(reason)}")
        accept_loop(listen_socket)
    end
  end

  defp handle_client(socket) do
    case :gen_tcp.recv(socket, 0) do
      {:ok, data} ->
        response = process_request(String.trim(data))
        :gen_tcp.send(socket, response <> "\n")
        handle_client(socket)

      {:error, :closed} ->
        :ok

      {:error, reason} ->
        Logger.debug("Client error: #{inspect(reason)}")
        :ok
    end
  end

  ## Request Processing

  defp process_request(data) do
    case Jason.decode(data) do
      {:ok, request} ->
        handle_jsonrpc(request)

      {:error, _} ->
        error_response(nil, -32700, "Parse error")
    end
  end

  defp handle_jsonrpc(%{"jsonrpc" => "2.0", "method" => method, "id" => id} = request) do
    params = Map.get(request, "params", %{})

    result = case method do
      "mkdir" -> handle_mkdir(params)
      "rmdir" -> handle_rmdir(params)
      "touch" -> handle_touch(params)
      "rm" -> handle_rm(params)
      "undo" -> handle_undo(params)
      "redo" -> handle_redo(params)
      "history" -> handle_history(params)
      "status" -> handle_status(params)
      "begin" -> handle_begin(params)
      "commit" -> handle_commit(params)
      "rollback" -> handle_rollback(params)
      "proofs" -> handle_proofs(params)
      _ -> {:error, -32601, "Method not found"}
    end

    case result do
      {:ok, data} -> success_response(id, data)
      {:error, code, message} -> error_response(id, code, message)
    end
  end

  defp handle_jsonrpc(_) do
    error_response(nil, -32600, "Invalid Request")
  end

  ## Method Handlers

  defp handle_mkdir(%{"path" => path}) do
    path_list = String.split(path, "/", trim: true)

    case VSH.Filesystem.mkdir(path_list, audit: true) do
      {:ok, :created} ->
        {:ok, op} = VSH.State.record_operation(:mkdir, path_list)
        proof = VSH.State.proof_for(:mkdir)

        {:ok, %{
          success: true,
          operation: "mkdir",
          path: path,
          operationId: op.id,
          undoCommand: "rmdir #{path}",
          proof: %{
            theorem: proof.theorem,
            location: proof.coq
          }
        }}

      {:error, reason} ->
        {:error, -32000, "mkdir failed: #{reason}"}
    end
  end

  defp handle_mkdir(_), do: {:error, -32602, "Invalid params: path required"}

  defp handle_rmdir(%{"path" => path}) do
    path_list = String.split(path, "/", trim: true)

    case VSH.Filesystem.rmdir(path_list, audit: true) do
      {:ok, :removed} ->
        {:ok, op} = VSH.State.record_operation(:rmdir, path_list)

        {:ok, %{
          success: true,
          operation: "rmdir",
          path: path,
          operationId: op.id,
          undoCommand: "mkdir #{path}"
        }}

      {:error, reason} ->
        {:error, -32000, "rmdir failed: #{reason}"}
    end
  end

  defp handle_rmdir(_), do: {:error, -32602, "Invalid params: path required"}

  defp handle_touch(%{"path" => path}) do
    path_list = String.split(path, "/", trim: true)

    case VSH.Filesystem.create_file(path_list, audit: true) do
      {:ok, :created} ->
        {:ok, op} = VSH.State.record_operation(:create_file, path_list)

        {:ok, %{
          success: true,
          operation: "touch",
          path: path,
          operationId: op.id,
          undoCommand: "rm #{path}"
        }}

      {:error, reason} ->
        {:error, -32000, "touch failed: #{reason}"}
    end
  end

  defp handle_touch(_), do: {:error, -32602, "Invalid params: path required"}

  defp handle_rm(%{"path" => path}) do
    path_list = String.split(path, "/", trim: true)
    path_str = VSH.Filesystem.path_to_string(path_list)

    # Read content for undo
    undo_data = case File.read(path_str) do
      {:ok, content} -> content
      _ -> nil
    end

    case VSH.Filesystem.delete_file(path_list, audit: true) do
      {:ok, :removed} ->
        {:ok, op} = VSH.State.record_operation(:delete_file, path_list, undo_data: undo_data)

        {:ok, %{
          success: true,
          operation: "rm",
          path: path,
          operationId: op.id,
          canUndo: undo_data != nil
        }}

      {:error, reason} ->
        {:error, -32000, "rm failed: #{reason}"}
    end
  end

  defp handle_rm(_), do: {:error, -32602, "Invalid params: path required"}

  defp handle_undo(params) do
    count = Map.get(params, "count", 1)
    operations = VSH.State.get_undoable(count)

    if operations == [] do
      {:ok, %{message: "Nothing to undo", undoneCount: 0}}
    else
      undone = Enum.reduce(operations, [], fn op, acc ->
        inverse = inverse_op(op.type)

        result = case inverse do
          :rmdir ->
            path_str = VSH.Filesystem.path_to_string(op.path)
            File.rmdir(path_str)

          :mkdir ->
            path_str = VSH.Filesystem.path_to_string(op.path)
            File.mkdir(path_str)

          :delete_file ->
            path_str = VSH.Filesystem.path_to_string(op.path)
            File.rm(path_str)

          :create_file ->
            path_str = VSH.Filesystem.path_to_string(op.path)
            content = op.undo_data || ""
            File.write(path_str, content)
        end

        case result do
          :ok ->
            undo_id = :crypto.strong_rand_bytes(8) |> Base.encode16(case: :lower)
            VSH.State.mark_undone(op.id, undo_id)
            VSH.State.push_redo(op)
            [%{originalOp: op.id, inverseOp: inverse, path: VSH.Filesystem.path_to_string(op.path)} | acc]

          _ ->
            acc
        end
      end)

      proof = VSH.State.proof_for(:undo)
      {:ok, %{
        undoneCount: length(undone),
        operations: Enum.reverse(undone),
        proof: %{theorem: proof.theorem}
      }}
    end
  end

  defp handle_redo(params) do
    count = Map.get(params, "count", 1)

    redone = Enum.reduce(1..count, [], fn _, acc ->
      case VSH.State.pop_redo() do
        nil -> acc
        op ->
          path_str = VSH.Filesystem.path_to_string(op.path)

          result = case op.type do
            :mkdir -> File.mkdir(path_str)
            :rmdir -> File.rmdir(path_str)
            :create_file -> File.write(path_str, "")
            :delete_file -> File.rm(path_str)
            _ -> {:error, :unsupported}
          end

          case result do
            :ok ->
              {:ok, _} = VSH.State.record_operation(op.type, op.path)
              [%{operation: op.type, path: path_str} | acc]
            _ ->
              acc
          end
      end
    end)

    {:ok, %{redoneCount: length(redone), operations: Enum.reverse(redone)}}
  end

  defp handle_history(params) do
    count = Map.get(params, "count", 10)
    show_proofs = Map.get(params, "showProofs", false)

    history = VSH.State.get_history(count)

    operations = Enum.map(history, fn op ->
      base = %{
        id: op.id,
        operation: op.type,
        path: VSH.Filesystem.path_to_string(op.path),
        timestamp: DateTime.to_iso8601(op.timestamp),
        undone: op.undone
      }

      if show_proofs do
        Map.put(base, :proof, op.proof_ref)
      else
        base
      end
    end)

    {:ok, %{count: length(operations), operations: operations}}
  end

  defp handle_status(_params) do
    {:ok, VSH.State.get_state()}
  end

  defp handle_begin(%{"name" => name}) do
    case VSH.State.begin_transaction(name) do
      {:ok, id} ->
        {:ok, %{
          success: true,
          transactionId: id,
          name: name,
          message: "Transaction started"
        }}

      {:error, reason} ->
        {:error, -32000, "begin failed: #{reason}"}
    end
  end

  defp handle_begin(_), do: {:error, -32602, "Invalid params: name required"}

  defp handle_commit(_params) do
    case VSH.State.commit_transaction() do
      {:ok, txn} ->
        {:ok, %{
          success: true,
          transactionId: txn.id,
          name: txn.name,
          operationCount: length(txn.operations)
        }}

      {:error, reason} ->
        {:error, -32000, "commit failed: #{reason}"}
    end
  end

  defp handle_rollback(_params) do
    case VSH.State.rollback_transaction() do
      {:ok, txn} ->
        # Undo all operations in the transaction
        operations = txn.operations
          |> Enum.reverse()
          |> Enum.map(fn op_id ->
            # Find and undo operation
            history = VSH.State.get_history(1000)
            Enum.find(history, &(&1.id == op_id))
          end)
          |> Enum.filter(&(&1 != nil))

        Enum.each(operations, fn op ->
          inverse = inverse_op(op.type)
          path_str = VSH.Filesystem.path_to_string(op.path)

          case inverse do
            :rmdir -> File.rmdir(path_str)
            :mkdir -> File.mkdir(path_str)
            :delete_file -> File.rm(path_str)
            :create_file ->
              content = op.undo_data || ""
              File.write(path_str, content)
          end

          VSH.State.mark_undone(op.id, "rollback")
        end)

        {:ok, %{
          success: true,
          transactionId: txn.id,
          name: txn.name,
          rolledBackOperations: length(operations)
        }}

      {:error, reason} ->
        {:error, -32000, "rollback failed: #{reason}"}
    end
  end

  defp handle_proofs(_params) do
    proofs = VSH.State.get_proofs()

    {:ok, %{
      totalTheorems: 256,
      proofSystems: 6,
      coreTheorems: proofs,
      verificationGap: "FFI layer implements precondition checks but is not mechanically verified"
    }}
  end

  ## Helpers

  defp inverse_op(:mkdir), do: :rmdir
  defp inverse_op(:rmdir), do: :mkdir
  defp inverse_op(:create_file), do: :delete_file
  defp inverse_op(:delete_file), do: :create_file
  defp inverse_op(:write_file), do: :write_file

  defp success_response(id, result) do
    Jason.encode!(%{
      jsonrpc: "2.0",
      id: id,
      result: result
    })
  end

  defp error_response(id, code, message) do
    Jason.encode!(%{
      jsonrpc: "2.0",
      id: id,
      error: %{code: code, message: message}
    })
  end
end
