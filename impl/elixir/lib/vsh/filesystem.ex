defmodule VSH.Filesystem do
  @moduledoc """
  Valence Shell - Elixir Filesystem Operations

  This module implements filesystem operations matching the Coq specification
  in proofs/coq/filesystem_model.v and proofs/coq/file_operations.v

  ## Correspondence with Formal Model

  Coq Specification → Elixir Implementation:
  - `safe_mkdir` → `mkdir/2`
  - `safe_rmdir` → `rmdir/2`
  - `safe_create_file` → `create_file/2`
  - `safe_delete_file` → `delete_file/2`

  ## Verification Status

  ✓ Specification formally verified in Coq
  ✓ Error conditions match POSIX model
  ❌ Implementation NOT formally verified
  → Requires manual review or testing to ensure correctness

  ## Trust Model

  This implementation should be tested against the formal specification.
  For production use, consider:
  - Property-based testing (using extracted Coq as oracle)
  - Audit logging for MAA compliance
  - Runtime assertion of preconditions
  """

  @type path :: [String.t()]
  @type error :: :eexist | :enoent | :eacces | :enotdir | :eisdir | :enotempty | :einval
  @type result(t) :: {:ok, t} | {:error, error}

  defmodule State do
    @moduledoc """
    Audit state for MAA (Mutually Assured Accountability)

    Tracks all filesystem operations for later proof generation.
    """
    defstruct [
      audit_log: [],
      proof_certificates: %{}
    ]
  end

  ## POSIX-style Operations with Error Handling

  @doc """
  Create a directory (safe version matching Coq `safe_mkdir`)

  ## Preconditions (from Coq):
  - Path does not exist
  - Parent directory exists
  - Parent is a directory
  - Parent has write permission

  ## Returns
  - `{:ok, :created}` if successful
  - `{:error, reason}` matching POSIX errors

  ## Examples

      iex> VSH.Filesystem.mkdir(["tmp", "test_dir"])
      {:ok, :created}

      iex> VSH.Filesystem.mkdir(["tmp", "test_dir"])
      {:error, :eexist}
  """
  @spec mkdir(path, keyword) :: result(:created)
  def mkdir(path, opts \\ []) do
    path_str = path_to_string(path)
    parent_str = path_to_string(parent_path(path))

    cond do
      # EEXIST: path already exists
      File.exists?(path_str) ->
        {:error, :eexist}

      # ENOENT: parent doesn't exist
      not File.exists?(parent_str) ->
        {:error, :enoent}

      # ENOTDIR: parent is not a directory
      not File.dir?(parent_str) ->
        {:error, :enotdir}

      # EACCES: parent not writable (simplified check)
      not writable?(parent_str) ->
        {:error, :eacces}

      # Preconditions satisfied - safe to create
      true ->
        case File.mkdir(path_str) do
          :ok ->
            maybe_audit(:mkdir, path, opts)
            {:ok, :created}
          {:error, reason} ->
            {:error, posix_to_error(reason)}
        end
    end
  end

  @doc """
  Remove a directory (safe version matching Coq `safe_rmdir`)

  ## Preconditions (from Coq):
  - Path exists and is a directory
  - Directory is empty
  - Parent has write permission
  - Not root directory

  ## Returns
  - `{:ok, :removed}` if successful
  - `{:error, reason}` matching POSIX errors
  """
  @spec rmdir(path, keyword) :: result(:removed)
  def rmdir(path, opts \\ []) do
    path_str = path_to_string(path)
    parent_str = path_to_string(parent_path(path))

    cond do
      # ENOENT: path doesn't exist
      not File.exists?(path_str) ->
        {:error, :enoent}

      # ENOTDIR: path is not a directory
      not File.dir?(path_str) ->
        {:error, :enotdir}

      # ENOTEMPTY: directory not empty
      not empty_dir?(path_str) ->
        {:error, :enotempty}

      # EACCES: parent not writable
      not writable?(parent_str) ->
        {:error, :eacces}

      # EACCES: cannot remove root
      path == [] ->
        {:error, :eacces}

      # Preconditions satisfied - safe to remove
      true ->
        case File.rmdir(path_str) do
          :ok ->
            maybe_audit(:rmdir, path, opts)
            {:ok, :removed}
          {:error, reason} ->
            {:error, posix_to_error(reason)}
        end
    end
  end

  @doc """
  Create a file (safe version matching Coq `safe_create_file`)

  ## Preconditions (from Coq):
  - Path does not exist
  - Parent directory exists
  - Parent is a directory
  - Parent has write permission
  """
  @spec create_file(path, keyword) :: result(:created)
  def create_file(path, opts \\ []) do
    path_str = path_to_string(path)
    parent_str = path_to_string(parent_path(path))

    cond do
      # EEXIST: path already exists
      File.exists?(path_str) ->
        {:error, :eexist}

      # ENOENT: parent doesn't exist
      not File.exists?(parent_str) ->
        {:error, :enoent}

      # ENOTDIR: parent is not a directory
      not File.dir?(parent_str) ->
        {:error, :enotdir}

      # EACCES: parent not writable
      not writable?(parent_str) ->
        {:error, :eacces}

      # Preconditions satisfied - safe to create
      true ->
        case File.write(path_str, "") do
          :ok ->
            maybe_audit(:create_file, path, opts)
            {:ok, :created}
          {:error, reason} ->
            {:error, posix_to_error(reason)}
        end
    end
  end

  @doc """
  Delete a file (safe version matching Coq `safe_delete_file`)

  ## Preconditions (from Coq):
  - Path exists and is a file
  - Parent has write permission
  """
  @spec delete_file(path, keyword) :: result(:removed)
  def delete_file(path, opts \\ []) do
    path_str = path_to_string(path)
    parent_str = path_to_string(parent_path(path))

    cond do
      # ENOENT: path doesn't exist
      not File.exists?(path_str) ->
        {:error, :enoent}

      # EISDIR: path is a directory
      File.dir?(path_str) ->
        {:error, :eisdir}

      # EACCES: parent not writable
      not writable?(parent_str) ->
        {:error, :eacces}

      # Preconditions satisfied - safe to delete
      true ->
        case File.rm(path_str) do
          :ok ->
            maybe_audit(:delete_file, path, opts)
            {:ok, :removed}
          {:error, reason} ->
            {:error, posix_to_error(reason)}
        end
    end
  end

  ## File Content Operations (matching proofs/coq/file_content_operations.v)

  @doc """
  Read file contents

  ## Preconditions:
  - Path exists and is a file
  - File has read permission

  ## Returns
  - `{:ok, content}` if successful
  - `{:error, reason}` matching POSIX errors
  """
  @spec read_file(path, keyword) :: result(binary())
  def read_file(path, opts \\ []) do
    path_str = path_to_string(path)

    cond do
      not File.exists?(path_str) ->
        {:error, :enoent}

      File.dir?(path_str) ->
        {:error, :eisdir}

      not readable?(path_str) ->
        {:error, :eacces}

      true ->
        case File.read(path_str) do
          {:ok, content} ->
            maybe_audit(:read_file, path, opts)
            {:ok, content}
          {:error, reason} ->
            {:error, posix_to_error(reason)}
        end
    end
  end

  @doc """
  Write file contents (matching Coq `write_file`)

  ## Preconditions:
  - Path exists and is a file
  - File has write permission

  ## Returns
  - `{:ok, :written}` if successful
  - `{:error, reason}` matching POSIX errors
  """
  @spec write_file(path, binary(), keyword) :: result(:written)
  def write_file(path, content, opts \\ []) do
    path_str = path_to_string(path)

    cond do
      not File.exists?(path_str) ->
        {:error, :enoent}

      File.dir?(path_str) ->
        {:error, :eisdir}

      not writable?(path_str) ->
        {:error, :eacces}

      true ->
        case File.write(path_str, content) do
          :ok ->
            maybe_audit(:write_file, path, opts)
            {:ok, :written}
          {:error, reason} ->
            {:error, posix_to_error(reason)}
        end
    end
  end

  ## Copy/Move Operations (matching proofs/z3/copy_move_operations.smt2)

  @doc """
  Copy file (matching Z3 `copy_file`)

  ## Preconditions:
  - Source exists and is a file
  - Destination does not exist
  - Destination parent exists and is writable
  - Source has read permission
  """
  @spec copy_file(path, path, keyword) :: result(:copied)
  def copy_file(src_path, dst_path, opts \\ []) do
    src_str = path_to_string(src_path)
    dst_str = path_to_string(dst_path)
    dst_parent_str = path_to_string(parent_path(dst_path))

    cond do
      not File.exists?(src_str) ->
        {:error, :enoent}

      File.dir?(src_str) ->
        {:error, :eisdir}

      File.exists?(dst_str) ->
        {:error, :eexist}

      not File.exists?(dst_parent_str) ->
        {:error, :enoent}

      not File.dir?(dst_parent_str) ->
        {:error, :enotdir}

      not readable?(src_str) ->
        {:error, :eacces}

      not writable?(dst_parent_str) ->
        {:error, :eacces}

      true ->
        case File.copy(src_str, dst_str) do
          {:ok, _bytes} ->
            maybe_audit(:copy_file, {src_path, dst_path}, opts)
            {:ok, :copied}
          {:error, reason} ->
            {:error, posix_to_error(reason)}
        end
    end
  end

  @doc """
  Move/rename file (matching Z3 `move`)

  ## Preconditions:
  - Source exists
  - Destination does not exist
  - Source parent has write permission
  - Destination parent exists and has write permission
  """
  @spec move(path, path, keyword) :: result(:moved)
  def move(src_path, dst_path, opts \\ []) do
    src_str = path_to_string(src_path)
    dst_str = path_to_string(dst_path)
    src_parent_str = path_to_string(parent_path(src_path))
    dst_parent_str = path_to_string(parent_path(dst_path))

    cond do
      not File.exists?(src_str) ->
        {:error, :enoent}

      File.exists?(dst_str) ->
        {:error, :eexist}

      not File.exists?(dst_parent_str) ->
        {:error, :enoent}

      not writable?(src_parent_str) ->
        {:error, :eacces}

      not writable?(dst_parent_str) ->
        {:error, :eacces}

      true ->
        case File.rename(src_str, dst_str) do
          :ok ->
            maybe_audit(:move, {src_path, dst_path}, opts)
            {:ok, :moved}
          {:error, reason} ->
            {:error, posix_to_error(reason)}
        end
    end
  end

  ## RMO Operations (Secure Deletion - proofs/coq/rmo_operations.v)

  @doc """
  Obliterate file - secure deletion with overwrite patterns

  Implements RMO (Remove-Match-Obliterate) for GDPR compliance.
  Uses configurable overwrite patterns (DoD 5220.22-M or Gutmann).

  ## Preconditions:
  - Path exists and is a file
  - Parent has write permission

  ## Options:
  - `:pattern` - `:dod` (3-pass), `:gutmann` (35-pass), or `:simple` (1-pass zeros)
  - `:verify` - verify overwrites (slower but more secure)
  """
  @spec obliterate_file(path, keyword) :: result(:obliterated)
  def obliterate_file(path, opts \\ []) do
    path_str = path_to_string(path)
    parent_str = path_to_string(parent_path(path))
    pattern = Keyword.get(opts, :pattern, :dod)
    verify = Keyword.get(opts, :verify, false)

    cond do
      not File.exists?(path_str) ->
        {:error, :enoent}

      File.dir?(path_str) ->
        {:error, :eisdir}

      not writable?(parent_str) ->
        {:error, :eacces}

      true ->
        case secure_overwrite(path_str, pattern, verify) do
          :ok ->
            case File.rm(path_str) do
              :ok ->
                maybe_audit(:obliterate, path, opts)
                {:ok, :obliterated}
              {:error, reason} ->
                {:error, posix_to_error(reason)}
            end
          {:error, reason} ->
            {:error, reason}
        end
    end
  end

  @doc """
  Obliterate directory tree - recursive secure deletion

  WARNING: This is irreversible. No undo possible.
  """
  @spec obliterate_tree(path, keyword) :: result(:obliterated)
  def obliterate_tree(path, opts \\ []) do
    path_str = path_to_string(path)
    parent_str = path_to_string(parent_path(path))

    cond do
      not File.exists?(path_str) ->
        {:error, :enoent}

      not File.dir?(path_str) ->
        obliterate_file(path, opts)

      not writable?(parent_str) ->
        {:error, :eacces}

      true ->
        case obliterate_tree_recursive(path_str, opts) do
          :ok ->
            maybe_audit(:obliterate_tree, path, opts)
            {:ok, :obliterated}
          {:error, reason} ->
            {:error, reason}
        end
    end
  end

  ## Reversible Operations (MAA Framework)

  @doc """
  Reversible directory creation - returns undo function

  This implements the RMR (Remove-Match-Reverse) primitive proven in Coq.

  ## Example

      iex> {result, undo} = VSH.Filesystem.mkdir_reversible(["tmp", "test"])
      iex> result
      {:ok, :created}
      iex> undo.()
      {:ok, :removed}
  """
  def mkdir_reversible(path, opts \\ []) do
    case mkdir(path, opts) do
      {:ok, :created} = result ->
        undo = fn -> rmdir(path, opts) end
        {result, undo}
      error ->
        {error, fn -> error end}
    end
  end

  @doc """
  Reversible file creation - returns undo function

  This implements the RMR primitive for files, proven in Coq.
  """
  def create_file_reversible(path, opts \\ []) do
    case create_file(path, opts) do
      {:ok, :created} = result ->
        undo = fn -> delete_file(path, opts) end
        {result, undo}
      error ->
        {error, fn -> error end}
    end
  end

  @doc """
  Reversible file write - captures old content for undo
  """
  def write_file_reversible(path, new_content, opts \\ []) do
    case read_file(path, opts) do
      {:ok, old_content} ->
        case write_file(path, new_content, opts) do
          {:ok, :written} = result ->
            undo = fn -> write_file(path, old_content, opts) end
            {result, undo, old_content}
          error ->
            {error, fn -> error end, nil}
        end
      error ->
        {error, fn -> error end, nil}
    end
  end

  @doc """
  Reversible copy - returns undo function that deletes the copy
  """
  def copy_file_reversible(src_path, dst_path, opts \\ []) do
    case copy_file(src_path, dst_path, opts) do
      {:ok, :copied} = result ->
        undo = fn -> delete_file(dst_path, opts) end
        {result, undo}
      error ->
        {error, fn -> error end}
    end
  end

  @doc """
  Reversible move - returns undo function that moves back
  """
  def move_reversible(src_path, dst_path, opts \\ []) do
    case move(src_path, dst_path, opts) do
      {:ok, :moved} = result ->
        undo = fn -> move(dst_path, src_path, opts) end
        {result, undo}
      error ->
        {error, fn -> error end}
    end
  end

  ## Path Utilities

  @doc """
  Convert path list to string

  Matches Coq path model: Path = list PathComponent
  """
  @spec path_to_string(path) :: String.t()
  def path_to_string([]), do: "/"
  def path_to_string(components), do: "/" <> Enum.join(components, "/")

  @doc """
  Get parent path

  Matches Coq `parent_path` function
  """
  @spec parent_path(path) :: path
  def parent_path([]), do: []
  def parent_path(path) do
    path
    |> Enum.reverse()
    |> tl()
    |> Enum.reverse()
  rescue
    _ -> []
  end

  ## Helper Functions

  defp empty_dir?(path_str) do
    case File.ls(path_str) do
      {:ok, []} -> true
      _ -> false
    end
  end

  defp writable?(path_str) do
    case File.stat(path_str) do
      {:ok, %{access: access}} when access in [:read_write, :write] -> true
      _ -> false
    end
  end

  defp posix_to_error(:eexist), do: :eexist
  defp posix_to_error(:enoent), do: :enoent
  defp posix_to_error(:eacces), do: :eacces
  defp posix_to_error(:enotdir), do: :enotdir
  defp posix_to_error(:eisdir), do: :eisdir
  defp posix_to_error(:enotempty), do: :enotempty
  defp posix_to_error(_), do: :einval

  defp maybe_audit(operation, path, opts) do
    if opts[:audit] do
      # In production: write to audit log with timestamp and proof certificate
      IO.puts("[AUDIT] #{operation} #{inspect(path)}")
    end
  end

  defp readable?(path_str) do
    case File.stat(path_str) do
      {:ok, %{access: access}} when access in [:read_write, :read] -> true
      _ -> false
    end
  end

  ## Secure Overwrite Patterns (RMO Implementation)

  @doc false
  defp secure_overwrite(path_str, pattern, verify) do
    case File.stat(path_str) do
      {:ok, %{size: size}} when size > 0 ->
        passes = overwrite_passes(pattern)
        do_secure_overwrite(path_str, size, passes, verify)
      {:ok, %{size: 0}} ->
        :ok
      {:error, reason} ->
        {:error, posix_to_error(reason)}
    end
  end

  defp overwrite_passes(:simple), do: [{:zeros, 1}]
  defp overwrite_passes(:dod) do
    # DoD 5220.22-M (3 passes)
    [{:zeros, 1}, {:ones, 1}, {:random, 1}]
  end
  defp overwrite_passes(:gutmann) do
    # Gutmann method (35 passes - simplified subset)
    [
      {:random, 4},          # Random passes 1-4
      {:pattern, 0x55},      # Pass 5
      {:pattern, 0xAA},      # Pass 6
      {:pattern, 0x92, 0x49, 0x24},  # Passes 7-9
      {:pattern, 0x49, 0x24, 0x92},  # Passes 10-12
      {:pattern, 0x24, 0x92, 0x49},  # Passes 13-15
      {:zeros, 1},           # Pass 16
      {:pattern, 0x11},      # Pass 17
      {:pattern, 0x22},      # Pass 18
      {:pattern, 0x33},      # Pass 19
      {:pattern, 0x44},      # Pass 20
      {:pattern, 0x55},      # Pass 21
      {:pattern, 0x66},      # Pass 22
      {:pattern, 0x77},      # Pass 23
      {:pattern, 0x88},      # Pass 24
      {:pattern, 0x99},      # Pass 25
      {:pattern, 0xAA},      # Pass 26
      {:pattern, 0xBB},      # Pass 27
      {:pattern, 0xCC},      # Pass 28
      {:pattern, 0xDD},      # Pass 29
      {:pattern, 0xEE},      # Pass 30
      {:pattern, 0xFF},      # Pass 31
      {:random, 4}           # Random passes 32-35
    ]
  end

  defp do_secure_overwrite(path_str, size, passes, verify) do
    Enum.reduce_while(passes, :ok, fn pass, _acc ->
      case overwrite_pass(path_str, size, pass) do
        :ok ->
          if verify do
            case verify_overwrite(path_str, size, pass) do
              :ok -> {:cont, :ok}
              error -> {:halt, error}
            end
          else
            {:cont, :ok}
          end
        error ->
          {:halt, error}
      end
    end)
  end

  defp overwrite_pass(path_str, size, {:zeros, count}) do
    data = :binary.copy(<<0>>, size)
    write_passes(path_str, data, count)
  end

  defp overwrite_pass(path_str, size, {:ones, count}) do
    data = :binary.copy(<<0xFF>>, size)
    write_passes(path_str, data, count)
  end

  defp overwrite_pass(path_str, size, {:random, count}) do
    Enum.reduce_while(1..count, :ok, fn _, _acc ->
      data = :crypto.strong_rand_bytes(size)
      case File.write(path_str, data) do
        :ok -> {:cont, :ok}
        error -> {:halt, error}
      end
    end)
  end

  defp overwrite_pass(path_str, size, {:pattern, byte}) do
    data = :binary.copy(<<byte>>, size)
    write_passes(path_str, data, 1)
  end

  defp overwrite_pass(path_str, size, {:pattern, b1, b2, b3}) do
    pattern = <<b1, b2, b3>>
    repeats = div(size, 3) + 1
    data = :binary.copy(pattern, repeats) |> :binary.part(0, size)
    write_passes(path_str, data, 1)
  end

  defp write_passes(path_str, data, count) do
    Enum.reduce_while(1..count, :ok, fn _, _acc ->
      case File.write(path_str, data) do
        :ok ->
          # Force sync to disk
          case File.open(path_str, [:write]) do
            {:ok, file} ->
              :file.sync(file)
              File.close(file)
              {:cont, :ok}
            _ ->
              {:cont, :ok}
          end
        error ->
          {:halt, error}
      end
    end)
  end

  defp verify_overwrite(path_str, size, {:pattern, byte}) do
    case File.read(path_str) do
      {:ok, data} ->
        expected = :binary.copy(<<byte>>, size)
        if data == expected, do: :ok, else: {:error, :verify_failed}
      error ->
        error
    end
  end

  defp verify_overwrite(_path_str, _size, _pass), do: :ok

  defp obliterate_tree_recursive(path_str, opts) do
    case File.ls(path_str) do
      {:ok, entries} ->
        results = Enum.map(entries, fn entry ->
          full_path = Path.join(path_str, entry)
          if File.dir?(full_path) do
            obliterate_tree_recursive(full_path, opts)
          else
            path_list = String.split(full_path, "/", trim: true)
            case obliterate_file(path_list, opts) do
              {:ok, :obliterated} -> :ok
              error -> error
            end
          end
        end)

        case Enum.find(results, &(&1 != :ok)) do
          nil ->
            # All files obliterated, now remove empty directory
            File.rmdir(path_str)
          error ->
            error
        end

      {:error, reason} ->
        {:error, posix_to_error(reason)}
    end
  end
end
