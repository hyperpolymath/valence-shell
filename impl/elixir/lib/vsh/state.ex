# SPDX-License-Identifier: PLMP-1.0-or-later

defmodule VSH.State do
  @moduledoc """
  Valence Shell State Management

  GenServer that maintains:
  - Operation history with undo/redo capabilities
  - Transaction groupings
  - Audit log for MAA compliance
  - Proof references for each operation

  ## Formal Correspondence

  This state model corresponds to the Coq specification:
  - `FilesystemState` in filesystem_model.v
  - `OperationLog` in filesystem_composition.v
  """

  use GenServer

  @type operation_type :: :mkdir | :rmdir | :create_file | :delete_file | :write_file |
                          :read_file | :copy_file | :move | :obliterate | :obliterate_tree

  @type operation :: %{
    id: String.t(),
    type: operation_type,
    path: [String.t()],
    timestamp: DateTime.t(),
    undone: boolean(),
    undone_by: String.t() | nil,
    undo_data: binary() | nil,
    proof_ref: map()
  }

  @type transaction :: %{
    id: String.t(),
    name: String.t(),
    operations: [String.t()],
    start_time: DateTime.t(),
    committed: boolean()
  }

  @type state :: %{
    root: String.t(),
    history: [operation()],
    transactions: [transaction()],
    active_transaction: transaction() | nil,
    redo_stack: [operation()]
  }

  # Proof references matching Coq theorems
  @mkdir_rmdir_proof %{
    theorem: "mkdir_rmdir_reversible",
    coq: "proofs/coq/filesystem_model.v:L45-L62",
    lean4: "proofs/lean4/FilesystemModel.lean:L38-L52",
    agda: "proofs/agda/FilesystemModel.agda:L41-L58",
    isabelle: "proofs/isabelle/FilesystemModel.thy:L35-L50",
    description: "rmdir(mkdir(path, fs)) = fs when preconditions hold"
  }

  @create_delete_proof %{
    theorem: "create_delete_file_reversible",
    coq: "proofs/coq/file_operations.v:L32-L48",
    lean4: "proofs/lean4/FileOperations.lean:L28-L42",
    agda: "proofs/agda/FileOperations.agda:L30-L45",
    isabelle: "proofs/isabelle/FileOperations.thy:L25-L40",
    description: "delete_file(create_file(path, fs)) = fs when preconditions hold"
  }

  @composition_proof %{
    theorem: "operation_sequence_reversible",
    coq: "proofs/coq/filesystem_composition.v:L28-L52",
    lean4: "proofs/lean4/FilesystemComposition.lean:L24-L45",
    agda: "proofs/agda/FilesystemComposition.agda:L26-L48",
    isabelle: "proofs/isabelle/FilesystemComposition.thy:L22-L42",
    description: "apply_sequence(reverse(ops), apply_sequence(ops, fs)) = fs"
  }

  @content_ops_proof %{
    theorem: "write_file_reversible",
    coq: "proofs/coq/file_content_operations.v:L118-L135",
    isabelle: "proofs/isabelle/FileContentOperations.thy:L98-L134",
    mizar: "proofs/mizar/file_content_operations.miz:L118-L135",
    description: "write(p, old, write(p, new, fs)) = fs when preconditions hold"
  }

  @copy_move_proof %{
    theorem: "copy_preserves_source",
    z3: "proofs/z3/copy_move_operations.smt2:L140-L163",
    lean4: "proofs/lean4/CopyMoveOperations.lean:L78-L102",
    agda: "proofs/agda/CopyMoveOperations.agda:L85-L115",
    isabelle: "proofs/isabelle/CopyMoveOperations.thy:L92-L128",
    mizar: "proofs/mizar/copy_move_operations.miz:L95-L125",
    description: "copy(src, dst, fs) preserves src unchanged, creates dst with same content"
  }

  @move_reversible_proof %{
    theorem: "move_reversible",
    z3: "proofs/z3/copy_move_operations.smt2:L254-L269",
    lean4: "proofs/lean4/CopyMoveOperations.lean:L145-L175",
    agda: "proofs/agda/CopyMoveOperations.agda:L158-L188",
    isabelle: "proofs/isabelle/CopyMoveOperations.thy:L165-L195",
    mizar: "proofs/mizar/copy_move_operations.miz:L168-L198",
    description: "move(dst, src, move(src, dst, fs)) = fs"
  }

  @rmo_proof %{
    theorem: "obliterate_irreversible",
    coq: "proofs/coq/rmo_operations.v:L85-L115",
    lean4: "proofs/lean4/RMOOperations.lean:L78-L108",
    agda: "proofs/agda/RMOOperations.agda:L82-L112",
    isabelle: "proofs/isabelle/RMO_Operations.thy:L75-L105",
    mizar: "proofs/mizar/rmo_operations.miz:L80-L110",
    z3: "proofs/z3/rmo_operations.smt2:L95-L125",
    description: "RMO operations are provably irreversible - no inverse exists"
  }

  ## Client API

  def start_link(opts \\ []) do
    root = Keyword.get(opts, :root, "/tmp/vsh-sandbox")
    GenServer.start_link(__MODULE__, root, name: __MODULE__)
  end

  @doc "Get current state summary"
  def get_state do
    GenServer.call(__MODULE__, :get_state)
  end

  @doc "Record a new operation"
  def record_operation(type, path, opts \\ []) do
    GenServer.call(__MODULE__, {:record_operation, type, path, opts})
  end

  @doc "Get last N undoable operations"
  def get_undoable(count \\ 1) do
    GenServer.call(__MODULE__, {:get_undoable, count})
  end

  @doc "Mark operation as undone"
  def mark_undone(op_id, undo_id) do
    GenServer.call(__MODULE__, {:mark_undone, op_id, undo_id})
  end

  @doc "Push to redo stack"
  def push_redo(operation) do
    GenServer.call(__MODULE__, {:push_redo, operation})
  end

  @doc "Pop from redo stack"
  def pop_redo do
    GenServer.call(__MODULE__, :pop_redo)
  end

  @doc "Get operation history"
  def get_history(count \\ 10) do
    GenServer.call(__MODULE__, {:get_history, count})
  end

  @doc "Begin a transaction"
  def begin_transaction(name) do
    GenServer.call(__MODULE__, {:begin_transaction, name})
  end

  @doc "Commit current transaction"
  def commit_transaction do
    GenServer.call(__MODULE__, :commit_transaction)
  end

  @doc "Rollback current transaction"
  def rollback_transaction do
    GenServer.call(__MODULE__, :rollback_transaction)
  end

  @doc "Get proof references"
  def get_proofs do
    [
      @mkdir_rmdir_proof,
      @create_delete_proof,
      @composition_proof,
      @content_ops_proof,
      @copy_move_proof,
      @move_reversible_proof,
      @rmo_proof
    ]
  end

  @doc "Get proof for operation type"
  def proof_for(type) when type in [:mkdir, :rmdir], do: @mkdir_rmdir_proof
  def proof_for(type) when type in [:create_file, :delete_file], do: @create_delete_proof
  def proof_for(type) when type in [:read_file, :write_file], do: @content_ops_proof
  def proof_for(:copy_file), do: @copy_move_proof
  def proof_for(:move), do: @move_reversible_proof
  def proof_for(type) when type in [:obliterate, :obliterate_tree], do: @rmo_proof
  def proof_for(:undo), do: @composition_proof
  def proof_for(_), do: @composition_proof

  ## Server Callbacks

  @impl true
  def init(root) do
    File.mkdir_p!(root)

    state = %{
      root: root,
      history: [],
      transactions: [],
      active_transaction: nil,
      redo_stack: []
    }

    {:ok, state}
  end

  @impl true
  def handle_call(:get_state, _from, state) do
    summary = %{
      root: state.root,
      history_count: length(state.history),
      undoable_count: Enum.count(state.history, &(!&1.undone)),
      redo_count: length(state.redo_stack),
      active_transaction: state.active_transaction && state.active_transaction.name,
      transaction_count: length(state.transactions)
    }
    {:reply, summary, state}
  end

  @impl true
  def handle_call({:record_operation, type, path, opts}, _from, state) do
    operation = %{
      id: generate_id(),
      type: type,
      path: path,
      timestamp: DateTime.utc_now(),
      undone: false,
      undone_by: nil,
      undo_data: Keyword.get(opts, :undo_data),
      proof_ref: proof_for(type)
    }

    new_history = state.history ++ [operation]

    # Add to active transaction if present
    new_txn = case state.active_transaction do
      nil -> nil
      txn -> %{txn | operations: txn.operations ++ [operation.id]}
    end

    new_state = %{state |
      history: new_history,
      active_transaction: new_txn,
      redo_stack: []  # Clear redo on new operation
    }

    {:reply, {:ok, operation}, new_state}
  end

  @impl true
  def handle_call({:get_undoable, count}, _from, state) do
    undoable = state.history
      |> Enum.filter(&(!&1.undone))
      |> Enum.take(-count)

    {:reply, undoable, state}
  end

  @impl true
  def handle_call({:mark_undone, op_id, undo_id}, _from, state) do
    new_history = Enum.map(state.history, fn op ->
      if op.id == op_id do
        %{op | undone: true, undone_by: undo_id}
      else
        op
      end
    end)

    {:reply, :ok, %{state | history: new_history}}
  end

  @impl true
  def handle_call({:push_redo, operation}, _from, state) do
    {:reply, :ok, %{state | redo_stack: state.redo_stack ++ [operation]}}
  end

  @impl true
  def handle_call(:pop_redo, _from, state) do
    case state.redo_stack do
      [] -> {:reply, nil, state}
      stack ->
        {operation, rest} = List.pop_at(stack, -1)
        {:reply, operation, %{state | redo_stack: rest}}
    end
  end

  @impl true
  def handle_call({:get_history, count}, _from, state) do
    history = Enum.take(state.history, -count)
    {:reply, history, state}
  end

  @impl true
  def handle_call({:begin_transaction, name}, _from, state) do
    if state.active_transaction do
      {:reply, {:error, :transaction_active}, state}
    else
      txn = %{
        id: generate_id(),
        name: name,
        operations: [],
        start_time: DateTime.utc_now(),
        committed: false
      }
      {:reply, {:ok, txn.id}, %{state | active_transaction: txn}}
    end
  end

  @impl true
  def handle_call(:commit_transaction, _from, state) do
    case state.active_transaction do
      nil ->
        {:reply, {:error, :no_transaction}, state}
      txn ->
        committed = %{txn | committed: true}
        new_state = %{state |
          active_transaction: nil,
          transactions: state.transactions ++ [committed]
        }
        {:reply, {:ok, committed}, new_state}
    end
  end

  @impl true
  def handle_call(:rollback_transaction, _from, state) do
    case state.active_transaction do
      nil ->
        {:reply, {:error, :no_transaction}, state}
      txn ->
        {:reply, {:ok, txn}, %{state | active_transaction: nil}}
    end
  end

  ## Private Helpers

  defp generate_id do
    :crypto.strong_rand_bytes(8) |> Base.encode16(case: :lower)
  end
end
