defmodule Valence.Saga do
  @moduledoc """
  Saga pattern coordinator for compensating transactions.

  When a multi-step operation fails, the Saga ensures all completed
  steps are compensated (rolled back) in reverse order.

  ## The Saga Pattern

      Step 1 ──► Step 2 ──► Step 3 ──► FAIL!
                                         │
                                         ▼
      Comp 1 ◄── Comp 2 ◄── Comp 3 ◄────┘

  Each step records its compensation. On failure, compensations are
  executed in reverse order to restore the original state.

  ## Guarantees

  - Atomic: Either all steps complete, or all are rolled back
  - Idempotent: Re-execution with same key returns cached result
  - Recoverable: Pending sagas are recovered on restart
  """
  use GenServer

  alias Valence.{Journal, History, Command}

  # Client API

  def start_link(_opts) do
    GenServer.start_link(__MODULE__, %{}, name: __MODULE__)
  end

  @doc """
  Execute a command as a transaction.

  Returns `{:ok, result}` on success, `{:error, reason}` on failure.
  """
  def execute(command, args) when is_atom(command) do
    GenServer.call(__MODULE__, {:execute, command, args})
  end

  @doc """
  Execute a sequence of commands as a single transaction.

  If any step fails, all previous steps are compensated.
  """
  def execute_sequence(steps) when is_list(steps) do
    GenServer.call(__MODULE__, {:execute_sequence, steps})
  end

  # Server Callbacks

  @impl true
  def init(_) do
    # On startup, recover any pending transactions
    Process.send_after(self(), :recover_pending, 100)
    {:ok, %{}}
  end

  @impl true
  def handle_call({:execute, command, args}, _from, state) do
    result = execute_single(command, args)
    {:reply, result, state}
  end

  @impl true
  def handle_call({:execute_sequence, steps}, _from, state) do
    result = execute_sequence_internal(steps, [])
    {:reply, result, state}
  end

  @impl true
  def handle_info(:recover_pending, state) do
    recover_pending_transactions()
    {:noreply, state}
  end

  # Private Implementation

  defp execute_single(command, args) do
    # Check if already executed (idempotency)
    key = Journal.begin(command, args)

    if Journal.executed?(key) do
      Journal.get_result(key)
    else
      do_execute(command, args, key)
    end
  end

  defp do_execute(command, args, key) do
    # Assess risk level
    risk = command.describe(args)
    maybe_warn(risk)

    # Execute the command
    case command.execute(args, key) do
      {:ok, result, compensation} ->
        # Record success
        Journal.complete(key, result, compensation)

        # Add to history for undo
        History.push(%{
          command: command,
          args: args,
          result: result,
          compensation: compensation,
          timestamp: DateTime.utc_now(),
          idempotency_key: key
        })

        {:ok, result}

      {:error, reason} ->
        Journal.fail(key, reason)
        {:error, reason}
    end
  end

  defp execute_sequence_internal([], completed) do
    # All steps completed successfully
    {:ok, Enum.reverse(completed)}
  end

  defp execute_sequence_internal([{command, args} | rest], completed) do
    case execute_single(command, args) do
      {:ok, result} ->
        execute_sequence_internal(rest, [{command, args, result} | completed])

      {:error, reason} ->
        # Failure! Compensate all completed steps in reverse
        compensate_all(completed)
        {:error, reason}
    end
  end

  defp compensate_all(completed) do
    Enum.each(completed, fn {command, args, _result} ->
      # Get the compensation from journal and execute it
      command.compensate(args, "compensation-#{UUID.uuid4()}")
    end)
  end

  defp recover_pending_transactions do
    pending = Journal.pending_entries()

    Enum.each(pending, fn entry ->
      # Log recovery attempt
      IO.puts("[Valence.Saga] Recovering pending transaction: #{entry.key}")

      # For pending entries, we need to either:
      # 1. Verify the operation completed (Two Generals)
      # 2. Or compensate it
      case entry.command.verify(entry.args) do
        :ok ->
          # Operation actually completed, mark it
          Journal.complete(entry.key, :recovered, nil)

        {:drift, _expected, _actual} ->
          # Operation didn't complete, mark as failed
          Journal.fail(entry.key, :incomplete_on_recovery)
      end
    end)
  end

  defp maybe_warn(:danger) do
    IO.puts("[Valence] ⚠️  Executing dangerous operation")
  end

  defp maybe_warn(:warn) do
    IO.puts("[Valence] ⚡ Operation may have side effects")
  end

  defp maybe_warn(:safe), do: :ok
end
