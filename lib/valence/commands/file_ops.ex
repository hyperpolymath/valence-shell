defmodule Valence.Commands.FileOps do
  @moduledoc """
  Reversible file operations.

  Implements:
  - `touch` / `rm` (create/delete empty file)
  - `write` (with content capture for compensation)
  """

  defmodule Touch do
    @moduledoc "Create an empty file. Compensation: delete it."
    @behaviour Valence.Command

    @impl true
    def describe(%{path: _path}), do: :safe

    @impl true
    def execute(%{path: path}, _idempotency_key) do
      case File.touch(path) do
        :ok ->
          compensation = %{
            module: Rm,
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
      File.rm(path)
    end

    @impl true
    def verify(%{path: path}) do
      if File.exists?(path) do
        :ok
      else
        {:drift, :exists, :missing}
      end
    end
  end

  defmodule Rm do
    @moduledoc "Remove a file. Compensation: restore from captured content."
    @behaviour Valence.Command

    @impl true
    def describe(%{path: _path}), do: :danger  # Destroys data

    @impl true
    def execute(%{path: path}, _idempotency_key) do
      # Capture content BEFORE deletion for compensation
      case File.read(path) do
        {:ok, content} ->
          case File.rm(path) do
            :ok ->
              compensation = %{
                module: __MODULE__,
                action: :restore,
                args: %{path: path, content: content}
              }
              {:ok, :removed, compensation}

            {:error, reason} ->
              {:error, reason}
          end

        {:error, :enoent} ->
          {:error, :file_not_found}

        {:error, reason} ->
          {:error, reason}
      end
    end

    @impl true
    def compensate(%{path: path, content: content}, _idempotency_key) do
      File.write(path, content)
    end

    def compensate(%{path: _path}, _idempotency_key) do
      # No content to restore (file was empty or not captured)
      {:error, :no_content_to_restore}
    end

    @impl true
    def verify(%{path: path}) do
      if File.exists?(path) do
        {:drift, :removed, :still_exists}
      else
        :ok
      end
    end
  end

  defmodule Write do
    @moduledoc "Write content to file. Compensation: restore previous content."
    @behaviour Valence.Command

    @impl true
    def describe(%{path: _path}), do: :warn

    @impl true
    def execute(%{path: path, content: new_content}, _idempotency_key) do
      # Capture old content for compensation
      old_content =
        case File.read(path) do
          {:ok, content} -> content
          {:error, :enoent} -> nil  # File didn't exist
        end

      case File.write(path, new_content) do
        :ok ->
          compensation = %{
            module: __MODULE__,
            action: :restore,
            args: %{path: path, content: old_content, existed: old_content != nil}
          }
          {:ok, :written, compensation}

        {:error, reason} ->
          {:error, reason}
      end
    end

    @impl true
    def compensate(%{path: path, content: nil, existed: false}, _idempotency_key) do
      # File didn't exist before, remove it
      File.rm(path)
    end

    def compensate(%{path: path, content: old_content}, _idempotency_key) do
      # Restore previous content
      File.write(path, old_content)
    end

    @impl true
    def verify(%{path: path, content: expected}) do
      case File.read(path) do
        {:ok, ^expected} -> :ok
        {:ok, actual} -> {:drift, expected, actual}
        {:error, _} -> {:drift, expected, :missing}
      end
    end
  end
end
