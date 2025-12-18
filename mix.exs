defmodule Valence.MixProject do
  use Mix.Project

  def project do
    [
      app: :valence,
      version: "0.1.0-alpha",
      elixir: "~> 1.15",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      dialyzer: [plt_add_apps: [:mix]],

      # Docs
      name: "Valence Shell",
      description: "Reversible shell with transactional semantics",
      source_url: "https://github.com/hyperpolymath/valence-shell",

      # Test
      test_coverage: [tool: ExCoveralls],
      preferred_cli_env: [
        coveralls: :test,
        "coveralls.detail": :test,
        "coveralls.html": :test
      ]
    ]
  end

  def application do
    [
      extra_applications: [:logger],
      mod: {Valence.Application, []}
    ]
  end

  defp deps do
    [
      # Transaction semantics (without DB backing)
      {:ecto, "~> 3.11"},

      # HTTP server (optional GUI/API)
      {:bandit, "~> 1.0"},

      # UUID generation for idempotency keys
      {:uuid, "~> 1.1"},

      # Development & Test
      {:stream_data, "~> 1.0", only: [:dev, :test]},
      {:credo, "~> 1.7", only: [:dev, :test], runtime: false},
      {:dialyxir, "~> 1.4", only: [:dev, :test], runtime: false},
      {:ex_doc, "~> 0.31", only: :dev, runtime: false}
    ]
  end
end
