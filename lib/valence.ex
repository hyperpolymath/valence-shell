defmodule Valence do
  @moduledoc """
  Valence Shell - The Thermodynamic Shell

  Every command is a reversible transaction. Every mutation is accountable.

  ## Core Principle

      F⁻¹(F(s)) = s

  Full reversibility without sacrificing POSIX compliance.

  ## Architecture

  - `Valence.Command` - Behaviour for reversible operations
  - `Valence.History.Zipper` - O(1) undo/redo structure
  - `Valence.Saga` - Compensating transaction orchestration
  - `Valence.Journal` - Idempotency and crash recovery
  """

  @doc """
  Execute a command with full transaction semantics.

  Returns `{:ok, result}` on success, `{:error, reason}` on failure.
  On failure, any partial mutations are automatically compensated.
  """
  def execute(command, args) do
    Valence.Saga.execute(command, args)
  end

  @doc """
  Undo the last operation.

  Returns `{:ok, previous_state}` or `{:error, :nothing_to_undo}`.
  """
  def undo do
    Valence.History.undo()
  end

  @doc """
  Redo the last undone operation.

  Returns `{:ok, restored_state}` or `{:error, :nothing_to_redo}`.
  """
  def redo do
    Valence.History.redo()
  end
end
