# SPDX-License-Identifier: AGPL-3.0-or-later

defmodule VSH.MixProject do
  use Mix.Project

  def project do
    [
      app: :vsh,
      version: "0.1.0",
      elixir: "~> 1.15",
      start_permanent: Mix.env() == :prod,
      compilers: [:elixir_make] ++ Mix.compilers(),
      make_targets: ["all"],
      make_clean: ["clean"],
      deps: deps(),
      description: "Valence Shell - Formally Verified Reversible Shell",
      package: package(),
      docs: docs()
    ]
  end

  def application do
    [
      extra_applications: [:logger, :crypto],
      mod: {VSH.Application, []}
    ]
  end

  defp deps do
    [
      {:jason, "~> 1.4"},
      {:elixir_make, "~> 0.8", runtime: false},
      {:ex_doc, "~> 0.31", only: :dev, runtime: false}
    ]
  end

  defp package do
    [
      name: "vsh",
      licenses: ["AGPL-3.0-or-later"],
      links: %{
        "GitHub" => "https://github.com/hyperpolymath/valence-shell"
      }
    ]
  end

  defp docs do
    [
      main: "VSH",
      extras: ["../../docs/PROGRESS_REPORT.md"]
    ]
  end
end
