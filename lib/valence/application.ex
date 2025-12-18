defmodule Valence.Application do
  @moduledoc """
  OTP Application for Valence Shell.

  Supervises:
  - History (Zipper state for undo/redo)
  - Journal (Idempotency log for crash recovery)
  - Saga (Compensating transaction coordinator)
  """
  use Application

  @impl true
  def start(_type, _args) do
    children = [
      # In-memory undo/redo history
      Valence.History,

      # Idempotency journal for crash recovery
      Valence.Journal,

      # Saga coordinator for multi-step transactions
      Valence.Saga
    ]

    opts = [strategy: :one_for_one, name: Valence.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
