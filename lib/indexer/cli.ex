defmodule Indexer.CLI do
  @moduledoc false

  def main(["version"]) do
    IO.puts("indexer #{Application.spec(:indexer, :vsn)}")
  end

  def main(["state-dir" | rest]) do
    root = List.first(rest) || File.cwd!()
    IO.puts(Indexer.state_dir(root))
  end

  def main(["service", "list" | rest]) do
    root = List.first(rest) || File.cwd!()
    catalog = Indexer.Services.Loader.load!(root)

    catalog.services
    |> Enum.map(fn service ->
      schedule = get_in(service, ["schedule", "type"]) || "unknown"
      enabled = if Map.get(service, "enabled", true), do: "enabled", else: "disabled"
      "#{service["id"]}\t#{service["phase"]}\t#{schedule}\t#{enabled}"
    end)
    |> Enum.each(&IO.puts/1)
  end

  def main(["service", "status" | rest]) do
    root = List.first(rest) || File.cwd!()
    root |> Indexer.Services.State.current() |> JSON.encode!() |> IO.puts()
  end

  def main(["service", "run", service_id | rest]) do
    root = List.first(rest) || File.cwd!()
    catalog = Indexer.Services.Loader.load!(root)

    with {:ok, service} <- Indexer.Services.Loader.get(catalog, service_id),
         {:ok, result} <- Indexer.Services.Runner.run(root, service) do
      result |> JSON.encode!() |> IO.puts()
    else
      {:error, :not_found} ->
        IO.puts(:stderr, "unknown service #{service_id}")
        System.halt(2)

      {:error, result} when is_map(result) ->
        result |> JSON.encode!() |> IO.puts()
        System.halt(Map.get(result, "exit_code", 1))

      {:error, reason} ->
        IO.puts(:stderr, inspect(reason))
        System.halt(1)
    end
  end

  def main(["work-item", "create", id, title | rest]) do
    root = List.first(rest) || File.cwd!()
    item = Indexer.WorkItems.create!(root, %{"id" => id, "title" => title})
    item |> JSON.encode!() |> IO.puts()
  end

  def main(["work-item", "list" | rest]) do
    root = List.first(rest) || File.cwd!()
    root |> Indexer.WorkItems.current() |> Map.values() |> JSON.encode!() |> IO.puts()
  end

  def main(["worker", "list" | rest]) do
    root = List.first(rest) || File.cwd!()
    root |> Indexer.Workers.current() |> Map.values() |> JSON.encode!() |> IO.puts()
  end

  def main(["worker", "run", worker_id | rest]) do
    root = List.first(rest) || File.cwd!()

    case Indexer.Workers.Runner.run(root, worker_id) do
      {:ok, result} ->
        result |> JSON.encode!() |> IO.puts()

      {:error, reason} ->
        IO.puts(:stderr, inspect(reason))
        System.halt(1)
    end
  end

  def main(["change-set", "list" | rest]) do
    root = List.first(rest) || File.cwd!()
    root |> Indexer.ChangeSets.current() |> Map.values() |> JSON.encode!() |> IO.puts()
  end

  def main(["change-set", "merge-plan" | rest]) do
    root = List.first(rest) || File.cwd!()

    root
    |> Indexer.ChangeSets.ready_for_merge()
    |> Indexer.ChangeSets.MergePlanner.select_batch()
    |> JSON.encode!()
    |> IO.puts()
  end

  def main(["control", "export" | rest]) do
    root = List.first(rest) || File.cwd!()
    root |> Indexer.ControlBranch.Exporter.export!() |> JSON.encode!() |> IO.puts()
  end

  def main(["control", "publish" | rest]) do
    root = List.first(rest) || File.cwd!()

    case Indexer.ControlBranch.Publisher.publish!(root) do
      {:ok, result} ->
        result |> JSON.encode!() |> IO.puts()

      {:error, error} ->
        error |> JSON.encode!() |> IO.puts()
        System.halt(1)
    end
  end

  def main(["control", "import" | rest]) do
    root = List.first(rest) || File.cwd!()
    root |> Indexer.ControlBranch.Importer.import!() |> JSON.encode!() |> IO.puts()
  end

  def main(["projection", "rebuild" | rest]) do
    root = List.first(rest) || File.cwd!()
    root |> Indexer.State.Projections.rebuild!() |> JSON.encode!() |> IO.puts()
  end

  def main(_args) do
    IO.puts("""
    indexer

    Commands:
      version
      state-dir [PROJECT_ROOT]
      service list [PROJECT_ROOT]
      service status [PROJECT_ROOT]
      service run SERVICE_ID [PROJECT_ROOT]
      work-item create ID TITLE [PROJECT_ROOT]
      work-item list [PROJECT_ROOT]
      worker list [PROJECT_ROOT]
      worker run WORKER_ID [PROJECT_ROOT]
      change-set list [PROJECT_ROOT]
      change-set merge-plan [PROJECT_ROOT]
      control export [PROJECT_ROOT]
      control publish [PROJECT_ROOT]
      control import [PROJECT_ROOT]
      projection rebuild [PROJECT_ROOT]
    """)
  end
end
