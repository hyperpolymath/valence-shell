# SPDX-License-Identifier: AGPL-3.0-or-later

defmodule VSH.NIF do
  @moduledoc """
  NIF bindings to the Zig FFI layer.

  This module provides direct access to the verified filesystem operations
  implemented in Zig with precondition checking derived from Coq proofs.

  ## Architecture

  ```
  Elixir (VSH.NIF) → NIF → Zig (valence_ffi) → POSIX syscalls
  ```

  ## Verification Status

  The Zig layer implements precondition checks matching:
  - `mkdir_precondition` from filesystem_model.v
  - `rmdir_precondition` from filesystem_model.v
  - `create_file_precondition` from file_operations.v
  - `delete_file_precondition` from file_operations.v
  """

  @on_load :load_nif

  def load_nif do
    nif_path = :code.priv_dir(:vsh) ++ ~c"/valence_ffi"

    case :erlang.load_nif(nif_path, 0) do
      :ok -> :ok
      {:error, {:reload, _}} -> :ok
      {:error, reason} -> {:error, reason}
    end
  end

  # NIF stubs - replaced at load time

  @doc """
  Create a directory with precondition checking.

  Returns:
  - `:ok` on success
  - `{:error, :eexist}` if path already exists
  - `{:error, :enoent}` if parent doesn't exist
  - `{:error, :enotdir}` if parent is not a directory
  - `{:error, :eacces}` if no write permission
  """
  @spec mkdir(String.t()) :: :ok | {:error, atom()}
  def mkdir(_path), do: :erlang.nif_error(:not_loaded)

  @doc """
  Remove an empty directory with precondition checking.

  Returns:
  - `:ok` on success
  - `{:error, :enoent}` if path doesn't exist
  - `{:error, :enotdir}` if not a directory
  - `{:error, :enotempty}` if directory not empty
  - `{:error, :eacces}` if no write permission on parent
  """
  @spec rmdir(String.t()) :: :ok | {:error, atom()}
  def rmdir(_path), do: :erlang.nif_error(:not_loaded)

  @doc """
  Create an empty file with precondition checking.

  Returns:
  - `:ok` on success
  - `{:error, :eexist}` if path already exists
  - `{:error, :enoent}` if parent doesn't exist
  - `{:error, :enotdir}` if parent is not a directory
  - `{:error, :eacces}` if no write permission
  """
  @spec create_file(String.t()) :: :ok | {:error, atom()}
  def create_file(_path), do: :erlang.nif_error(:not_loaded)

  @doc """
  Delete a file with precondition checking.

  Returns:
  - `:ok` on success
  - `{:error, :enoent}` if path doesn't exist
  - `{:error, :eisdir}` if path is a directory
  - `{:error, :eacces}` if no write permission on parent
  """
  @spec delete_file(String.t()) :: :ok | {:error, atom()}
  def delete_file(_path), do: :erlang.nif_error(:not_loaded)

  @doc """
  Get the last audit log entry.

  Returns the most recent operation recorded by the Zig FFI layer,
  including the proof reference for MAA compliance.
  """
  @spec get_last_audit() :: {:ok, map()} | {:error, :no_entries}
  def get_last_audit, do: :erlang.nif_error(:not_loaded)
end
