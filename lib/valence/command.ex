defmodule Valence.Command do
  @moduledoc """
  Behaviour for reversible shell commands.

  Every command in Valence Shell must implement these four callbacks,
  ensuring full reversibility and accountability.

  ## The Contract

  ```elixir
  @callback describe(args) :: :safe | :warn | :danger
  @callback execute(args, idempotency_key) :: {:ok, result, compensation} | {:error, reason}
  @callback compensate(args, idempotency_key) :: :ok | {:error, reason}
  @callback verify(args) :: :ok | {:drift, expected, actual}
  ```

  ## Example Implementation

  ```elixir
  defmodule Valence.Commands.Mkdir do
    @behaviour Valence.Command

    @impl true
    def describe(%{path: _path}), do: :safe

    @impl true
    def execute(%{path: path}, idempotency_key) do
      case File.mkdir(path) do
        :ok ->
          compensation = %{module: __MODULE__, action: :rmdir, args: %{path: path}}
          {:ok, :created, compensation}
        {:error, reason} ->
          {:error, reason}
      end
    end

    @impl true
    def compensate(%{path: path}, _idempotency_key) do
      File.rmdir(path)
    end

    @impl true
    def verify(%{path: path}) do
      if File.dir?(path), do: :ok, else: {:drift, :exists, :missing}
    end
  end
  ```
  """

  @type args :: map()
  @type idempotency_key :: binary()
  @type compensation :: %{module: module(), action: atom(), args: map()}
  @type risk_level :: :safe | :warn | :danger

  @doc """
  Assess the thermodynamic cost of this operation.

  - `:safe` - Reversible with no external effects
  - `:warn` - Reversible but may have observable side effects
  - `:danger` - May be irreversible or affect external systems
  """
  @callback describe(args()) :: risk_level()

  @doc """
  Execute the command and return its compensation.

  The idempotency key ensures crash recovery - if this key has already
  been executed, return the cached result instead of re-executing.

  Returns:
  - `{:ok, result, compensation}` - Success with undo information
  - `{:error, reason}` - Failure (no compensation needed)
  """
  @callback execute(args(), idempotency_key()) ::
              {:ok, term(), compensation()} | {:error, term()}

  @doc """
  Undo the effects of a previous execution.

  This is the inverse function: if `execute` did F(s), then
  `compensate` does F⁻¹(F(s)) = s.
  """
  @callback compensate(args(), idempotency_key()) :: :ok | {:error, term()}

  @doc """
  Verify the expected state matches reality.

  Used for Two Generals problem detection - did the operation actually
  complete, or is there drift between expected and actual state?
  """
  @callback verify(args()) :: :ok | {:drift, expected :: term(), actual :: term()}

  @doc """
  Check if a module implements the Command behaviour.
  """
  def command?(module) when is_atom(module) do
    behaviours = module.module_info(:attributes)[:behaviour] || []
    __MODULE__ in behaviours
  end
end
