defmodule Valence.Journal do
  @moduledoc """
  Idempotency journal for crash recovery.

  Every command execution is recorded with a unique idempotency key.
  On crash recovery, the journal is consulted to determine:

  1. Did this command complete successfully?
  2. If not, what compensation is needed?

  ## Idempotency Guarantee

  If a command with key K has already completed, re-executing with
  the same key returns the cached result instead of re-executing.

  ## Journal States

  - `:pending` - Command started but not completed
  - `:completed` - Command finished successfully
  - `:compensated` - Command was rolled back
  - `:failed` - Command failed (no compensation needed)
  """
  use GenServer

  defstruct entries: %{}

  @type state :: :pending | :completed | :compensated | :failed

  @type entry :: %{
          key: binary(),
          command: module(),
          args: map(),
          state: state(),
          result: term() | nil,
          compensation: map() | nil,
          started_at: DateTime.t(),
          completed_at: DateTime.t() | nil
        }

  # Client API

  def start_link(_opts) do
    GenServer.start_link(__MODULE__, %__MODULE__{}, name: __MODULE__)
  end

  @doc "Begin a new journal entry. Returns the idempotency key."
  def begin(command, args) do
    key = generate_key()
    GenServer.call(__MODULE__, {:begin, key, command, args})
    key
  end

  @doc "Check if a key has already been executed."
  def executed?(key) do
    GenServer.call(__MODULE__, {:executed?, key})
  end

  @doc "Get the cached result for a key (if completed)."
  def get_result(key) do
    GenServer.call(__MODULE__, {:get_result, key})
  end

  @doc "Mark a command as completed with its result and compensation."
  def complete(key, result, compensation) do
    GenServer.call(__MODULE__, {:complete, key, result, compensation})
  end

  @doc "Mark a command as failed."
  def fail(key, reason) do
    GenServer.call(__MODULE__, {:fail, key, reason})
  end

  @doc "Mark a command as compensated (rolled back)."
  def compensate(key) do
    GenServer.call(__MODULE__, {:compensate, key})
  end

  @doc "Get all pending entries (for crash recovery)."
  def pending_entries do
    GenServer.call(__MODULE__, :pending_entries)
  end

  # Server Callbacks

  @impl true
  def init(_) do
    {:ok, %__MODULE__{}}
  end

  @impl true
  def handle_call({:begin, key, command, args}, _from, state) do
    entry = %{
      key: key,
      command: command,
      args: args,
      state: :pending,
      result: nil,
      compensation: nil,
      started_at: DateTime.utc_now(),
      completed_at: nil
    }

    new_state = %{state | entries: Map.put(state.entries, key, entry)}
    {:reply, :ok, new_state}
  end

  @impl true
  def handle_call({:executed?, key}, _from, state) do
    case Map.get(state.entries, key) do
      nil -> {:reply, false, state}
      %{state: :completed} -> {:reply, true, state}
      _ -> {:reply, false, state}
    end
  end

  @impl true
  def handle_call({:get_result, key}, _from, state) do
    case Map.get(state.entries, key) do
      %{state: :completed, result: result} -> {:reply, {:ok, result}, state}
      _ -> {:reply, {:error, :not_found}, state}
    end
  end

  @impl true
  def handle_call({:complete, key, result, compensation}, _from, state) do
    case Map.get(state.entries, key) do
      nil ->
        {:reply, {:error, :not_found}, state}

      entry ->
        updated = %{entry |
          state: :completed,
          result: result,
          compensation: compensation,
          completed_at: DateTime.utc_now()
        }
        new_state = %{state | entries: Map.put(state.entries, key, updated)}
        {:reply, :ok, new_state}
    end
  end

  @impl true
  def handle_call({:fail, key, reason}, _from, state) do
    case Map.get(state.entries, key) do
      nil ->
        {:reply, {:error, :not_found}, state}

      entry ->
        updated = %{entry |
          state: :failed,
          result: {:error, reason},
          completed_at: DateTime.utc_now()
        }
        new_state = %{state | entries: Map.put(state.entries, key, updated)}
        {:reply, :ok, new_state}
    end
  end

  @impl true
  def handle_call({:compensate, key}, _from, state) do
    case Map.get(state.entries, key) do
      nil ->
        {:reply, {:error, :not_found}, state}

      entry ->
        updated = %{entry | state: :compensated, completed_at: DateTime.utc_now()}
        new_state = %{state | entries: Map.put(state.entries, key, updated)}
        {:reply, :ok, new_state}
    end
  end

  @impl true
  def handle_call(:pending_entries, _from, state) do
    pending =
      state.entries
      |> Map.values()
      |> Enum.filter(&(&1.state == :pending))

    {:reply, pending, state}
  end

  # Private

  defp generate_key do
    UUID.uuid4()
  end
end
