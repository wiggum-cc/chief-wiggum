defmodule Indexer.ControlBranch.ImporterTest do
  use ExUnit.Case, async: true

  alias Indexer.ControlBranch.Importer

  test "imports work item and change-set JSON records" do
    root = tmp_dir()
    control = Path.join(root, "control")
    File.mkdir_p!(Path.join(control, "work_items"))
    File.mkdir_p!(Path.join(control, "change_sets/cs-1"))

    File.write!(
      Path.join(control, "work_items/TASK-001.json"),
      JSON.encode!(%{
        id: "TASK-001",
        title: "Imported",
        body: "From control",
        status: "pending",
        dependencies: []
      })
    )

    File.write!(
      Path.join(control, "change_sets/cs-1/change_set.json"),
      JSON.encode!(%{
        id: "cs-1",
        work_item_id: "TASK-001",
        worker_id: "worker-1",
        work_branch: "indexer/work/TASK-001/worker-1",
        affected_files: ["lib/a.ex"],
        status: "ready"
      })
    )

    result = Importer.import!(root, input_dir: control)
    assert result["work_items"] == 1
    assert result["change_sets"] == 1

    assert {:ok, item} = Indexer.WorkItems.get(root, "TASK-001")
    assert item["title"] == "Imported"

    assert {:ok, change_set} = Indexer.ChangeSets.get(root, "cs-1")
    assert change_set["status"] == "ready"
  end

  test "updates existing imported records" do
    root = tmp_dir()
    control = Path.join(root, "control")
    File.mkdir_p!(Path.join(control, "work_items"))
    Indexer.WorkItems.create!(root, %{id: "TASK-001", title: "Old"})

    File.write!(
      Path.join(control, "work_items/TASK-001.json"),
      JSON.encode!(%{
        id: "TASK-001",
        title: "New",
        body: "",
        status: "not_planned",
        dependencies: []
      })
    )

    Importer.import!(root, input_dir: control)

    assert {:ok, item} = Indexer.WorkItems.get(root, "TASK-001")
    assert item["title"] == "New"
    assert item["status"] == "not_planned"
  end

  defp tmp_dir do
    path =
      Path.join(
        System.tmp_dir!(),
        "indexer-control-import-test-#{System.unique_integer([:positive])}"
      )

    File.rm_rf!(path)
    File.mkdir_p!(path)
    path
  end
end
