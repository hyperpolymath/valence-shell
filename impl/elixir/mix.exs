# SPDX-License-Identifier: PLMP-1.0-or-later

defmodule VSH.MixProject do
  use Mix.Project

  def project do
    [
      app: :vsh,
      version: "0.14.0",
      elixir: "~> 1.15",
      start_permanent: Mix.env() == :prod,
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
      {:rustler, "~> 0.37"},
      {:zigler, "~> 0.15", runtime: false},
      {:ex_doc, "~> 0.31", only: :dev, runtime: false}
    ]
  end

  defp package do
    [
      name: "vsh",
      licenses: ["PLMP-1.0-or-later"],
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
