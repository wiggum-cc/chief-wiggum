defmodule Indexer.State.JsonlTest do
  use ExUnit.Case, async: true

  alias Indexer.State.{Event, Jsonl}

  test "appends and reads event records" do
    root = tmp_dir()
    event = Event.new("work_items", "work_item.created", "work_1", %{title: "Test"})

    path = Jsonl.ledger_path(root, "work_items")
    written = Jsonl.append_event!(root, event)

    assert written["type"] == "work_item.created"
    assert [read] = Jsonl.read!(path)
    assert read["payload"]["title"] == "Test"
    assert read["stream"] == "work_items"
  end

  test "recovers partial trailing records" do
    path = Path.join(tmp_dir(), "events.jsonl")
    File.write!(path, JSON.encode!(%{ok: 1}) <> "\n{\"partial\"")

    assert :ok = Jsonl.recover!(path)
    assert [%{"ok" => 1}] = Jsonl.read!(path)
  end

  defp tmp_dir do
    path =
      Path.join(System.tmp_dir!(), "indexer-jsonl-test-#{System.unique_integer([:positive])}")

    File.rm_rf!(path)
    File.mkdir_p!(path)
    path
  end
end
