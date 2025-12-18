defmodule Valence.Commands.Directory do
  @moduledoc """
  Reversible directory operations.

  Implements:
  - `mkdir` / `rmdir` (proven reversible: rmdir(mkdir(p)) = identity)
  """

  defmodule Mkdir do
    @moduledoc "Create a directory. Compensation: remove it."
    @behaviour Valence.Command

    @impl true
    def describe(%{path: _path}), do: :safe

    @impl true
    def execute(%{path: path}, _idempotency_key) do
      case File.mkdir_p(path) do
        :ok ->
          compensation = %{
            module: Rmdir,
            action: :compensate,
            args: %{path: path}
          }
          {:ok, :created, compensation}

        {:error, reason} ->
          {:error, reason}
      end
    end

    @impl true
    def compensate(%{path: path}, _idempotency_key) do
      case File.rmdir(path) do
        :ok -> :ok
        {:error, reason} -> {:error, reason}
      end
    end

    @impl true
    def verify(%{path: path}) do
      if File.dir?(path) do
        :ok
      else
        {:drift, :directory_exists, :missing}
      end
    end
  end

  defmodule Rmdir do
    @moduledoc "Remove an empty directory. Compensation: recreate it."
    @behaviour Valence.Command

    @impl true
    def describe(%{path: _path}), do: :warn  # Could fail if not empty

    @impl true
    def execute(%{path: path}, _idempotency_key) do
      # Capture state for compensation
      case File.rmdir(path) do
        :ok ->
          compensation = %{
            module: Mkdir,
            action: :compensate,
            args: %{path: path}
          }
          {:ok, :removed, compensation}

        {:error, reason} ->
          {:error, reason}
      end
    end

    @impl true
    def compensate(%{path: path}, _idempotency_key) do
      File.mkdir_p(path)
    end

    @impl true
    def verify(%{path: path}) do
      if File.dir?(path) do
        {:drift, :removed, :still_exists}
      else
        :ok
      end
    end
  end
end
