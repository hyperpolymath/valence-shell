defmodule Valence.History.Zipper do
  @moduledoc """
  A Zipper data structure for O(1) undo/redo.

  The Zipper is a cursor into a list, maintaining both the elements
  before the cursor (past) and after it (future). This enables
  efficient bidirectional navigation without copying.

  ## Conceptual Model

      Past (reversed)     Cursor     Future
      [c, b, a]            |        [d, e, f]

      Timeline: a → b → c → | → d → e → f
                           ^
                        Current

  ## Complexity

  - `push/2` - O(1)
  - `back/1` - O(1)
  - `forward/1` - O(1)

  ## Why Zipper?

  Traditional history implementations copy the entire state on each
  operation. A Zipper stores only the deltas (commands + compensations),
  making it memory-efficient for long sessions.
  """

  defstruct past: [], future: []

  @type entry :: %{
          command: module(),
          args: map(),
          result: term(),
          compensation: map(),
          timestamp: DateTime.t(),
          idempotency_key: binary()
        }

  @type t :: %__MODULE__{
          past: [entry()],
          future: [entry()]
        }

  @doc """
  Create a new empty Zipper.
  """
  def new, do: %__MODULE__{}

  @doc """
  Add an entry to the history.

  This clears the future (redo stack), as we're branching from
  the current point in time.
  """
  @spec push(t(), entry()) :: t()
  def push(%__MODULE__{past: past}, entry) do
    %__MODULE__{
      past: [entry | past],
      future: []  # Clear redo stack on new action
    }
  end

  @doc """
  Move backward in history (undo).

  Returns `{:ok, entry, new_zipper}` or `:empty`.
  """
  @spec back(t()) :: {:ok, entry(), t()} | :empty
  def back(%__MODULE__{past: []}), do: :empty

  def back(%__MODULE__{past: [entry | rest], future: future}) do
    new_zipper = %__MODULE__{
      past: rest,
      future: [entry | future]
    }
    {:ok, entry, new_zipper}
  end

  @doc """
  Move forward in history (redo).

  Returns `{:ok, entry, new_zipper}` or `:empty`.
  """
  @spec forward(t()) :: {:ok, entry(), t()} | :empty
  def forward(%__MODULE__{future: []}), do: :empty

  def forward(%__MODULE__{past: past, future: [entry | rest]}) do
    new_zipper = %__MODULE__{
      past: [entry | past],
      future: rest
    }
    {:ok, entry, new_zipper}
  end

  @doc """
  Get the current entry (most recent in past).
  """
  @spec current(t()) :: {:ok, entry()} | :empty
  def current(%__MODULE__{past: []}), do: :empty
  def current(%__MODULE__{past: [entry | _]}), do: {:ok, entry}

  @doc """
  Count of entries in past (available undos).
  """
  @spec undo_count(t()) :: non_neg_integer()
  def undo_count(%__MODULE__{past: past}), do: length(past)

  @doc """
  Count of entries in future (available redos).
  """
  @spec redo_count(t()) :: non_neg_integer()
  def redo_count(%__MODULE__{future: future}), do: length(future)
end
