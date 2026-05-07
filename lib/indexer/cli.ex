defmodule Indexer.CLI do
  @moduledoc false

  def main(["version"]) do
    IO.puts("indexer #{Application.spec(:indexer, :vsn)}")
  end

  def main(["state-dir" | rest]) do
    root = List.first(rest) || File.cwd!()
    IO.puts(Indexer.state_dir(root))
  end

  def main(_args) do
    IO.puts("""
    indexer

    Commands:
      version
      state-dir [PROJECT_ROOT]
    """)
  end
end
