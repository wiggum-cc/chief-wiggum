defmodule Indexer.MixProject do
  use Mix.Project

  def project do
    [
      app: :indexer,
      version: "0.1.0",
      elixir: "~> 1.19",
      start_permanent: Mix.env() == :prod,
      deps: [],
      escript: [main_module: Indexer.CLI],
      aliases: aliases()
    ]
  end

  def application do
    [
      extra_applications: [:crypto, :logger],
      mod: {Indexer.Application, []}
    ]
  end

  defp aliases do
    [
      check: ["format --check-formatted", "compile --warnings-as-errors", "test"]
    ]
  end
end
