defmodule Valence.History do
  @moduledoc """
  In-memory command history using a Zipper structure.

  Provides O(1) undo/redo without copying entire state.
  The Zipper maintains a cursor position in a doubly-linked list,
  enabling efficient navigation forward and backward.

  ## Structure

      %Zipper{
        past: [cmd3, cmd2, cmd1],  # Most recent first
        future: [cmd4, cmd5]       # Next to redo first
      }

  ## Operations

  - `push/1` - Add command to history (clears redo stack)
  - `undo/0` - Move back one step, return compensation
  - `redo/0` - Move forward one step, return command
  """
  use GenServer

  alias Valence.History.Zipper

  # Client API

  def start_link(_opts) do
    GenServer.start_link(__MODULE__, %Zipper{}, name: __MODULE__)
  end

  @doc "Add a command to history. Clears any redo stack."
  def push(entry) do
    GenServer.call(__MODULE__, {:push, entry})
  end

  @doc "Undo the last command. Returns the compensation to execute."
  def undo do
    GenServer.call(__MODULE__, :undo)
  end

  @doc "Redo the last undone command. Returns the command to re-execute."
  def redo do
    GenServer.call(__MODULE__, :redo)
  end

  @doc "Get the current history state (for debugging)."
  def state do
    GenServer.call(__MODULE__, :state)
  end

  @doc "Clear all history."
  def clear do
    GenServer.call(__MODULE__, :clear)
  end

  # Server Callbacks

  @impl true
  def init(_) do
    {:ok, %Zipper{}}
  end

  @impl true
  def handle_call({:push, entry}, _from, zipper) do
    new_zipper = Zipper.push(zipper, entry)
    {:reply, :ok, new_zipper}
  end

  @impl true
  def handle_call(:undo, _from, zipper) do
    case Zipper.back(zipper) do
      {:ok, entry, new_zipper} ->
        {:reply, {:ok, entry}, new_zipper}

      :empty ->
        {:reply, {:error, :nothing_to_undo}, zipper}
    end
  end

  @impl true
  def handle_call(:redo, _from, zipper) do
    case Zipper.forward(zipper) do
      {:ok, entry, new_zipper} ->
        {:reply, {:ok, entry}, new_zipper}

      :empty ->
        {:reply, {:error, :nothing_to_redo}, zipper}
    end
  end

  @impl true
  def handle_call(:state, _from, zipper) do
    {:reply, zipper, zipper}
  end

  @impl true
  def handle_call(:clear, _from, _zipper) do
    {:reply, :ok, %Zipper{}}
  end
end
