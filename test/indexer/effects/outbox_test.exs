defmodule Indexer.Effects.OutboxTest do
  use ExUnit.Case, async: true

  alias Indexer.Effects.{Effect, Outbox}
  alias Indexer.State.Jsonl

  test "records pending and completed effects" do
    root = tmp_dir()
    effect = Effect.new("git.commit_workspace", "node_run", "node_1", %{message: "commit"})

    Outbox.record_pending!(root, effect)
    Outbox.mark_completed!(root, effect, %{commit_sha: "abc"})

    events = root |> Jsonl.ledger_path("effects") |> Jsonl.read!()
    assert Enum.map(events, & &1["type"]) == ["effect.pending", "effect.completed"]
    assert List.last(events)["payload"]["commit_sha"] == "abc"
  end

  defp tmp_dir do
    path =
      Path.join(System.tmp_dir!(), "indexer-outbox-test-#{System.unique_integer([:positive])}")

    File.rm_rf!(path)
    File.mkdir_p!(path)
    path
  end
end
