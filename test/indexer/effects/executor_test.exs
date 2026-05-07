defmodule Indexer.Effects.ExecutorTest do
  use ExUnit.Case, async: true

  alias Indexer.Effects.{Effect, Executor, Outbox}
  alias Indexer.WorkItems

  test "drains work item create effects and marks them completed" do
    root = tmp_dir()

    effect =
      Effect.new("work_item.create", "work_item", "TASK-001", %{
        "id" => "TASK-001",
        "title" => "Created by effect"
      })

    Outbox.record_pending!(root, effect)

    assert {:ok, result} = Executor.drain(root)
    assert result["attempted"] == 1
    assert result["completed"] == 1

    assert {:ok, item} = WorkItems.get(root, "TASK-001")
    assert item["title"] == "Created by effect"

    assert [%{"status" => "completed"}] = root |> Outbox.current() |> Map.values()
  end

  test "marks unsupported effects failed" do
    root = tmp_dir()
    effect = Effect.new("unknown.effect", "test", "scope-1", %{})
    Outbox.record_pending!(root, effect)

    assert {:ok, result} = Executor.drain(root)
    assert result["failed"] == 1

    assert [%{"status" => "failed", "attempts" => 1}] = root |> Outbox.current() |> Map.values()
  end

  test "schedules retry for failed effects until max attempts" do
    root = tmp_dir()
    effect = Effect.new("transient.effect", "test", "scope-1", %{})
    Outbox.record_pending!(root, effect)

    runner = fn _root, _effect -> {:error, %{"reason" => "transient"}} end

    assert {:ok, first} = Executor.drain(root, runner: runner, max_attempts: 2)
    assert first["attempted"] == 1
    assert first["retries"] == 1
    assert first["failed"] == 0
    assert [%{"status" => "pending", "attempts" => 1}] = root |> Outbox.current() |> Map.values()

    assert {:ok, second} = Executor.drain(root, runner: runner, max_attempts: 2)
    assert second["attempted"] == 1
    assert second["retries"] == 0
    assert second["failed"] == 1
    assert [%{"status" => "failed", "attempts" => 2}] = root |> Outbox.current() |> Map.values()
  end

  test "completes a retried effect on a later drain" do
    root = tmp_dir()
    effect = Effect.new("transient.effect", "test", "scope-1", %{})
    Outbox.record_pending!(root, effect)

    runner = fn _root, effect ->
      if effect.attempts == 0 do
        {:error, %{"reason" => "transient"}}
      else
        {:ok, %{"attempts" => effect.attempts + 1}}
      end
    end

    assert {:ok, first} = Executor.drain(root, runner: runner, max_attempts: 2)
    assert first["retries"] == 1

    assert {:ok, second} = Executor.drain(root, runner: runner, max_attempts: 2)
    assert second["completed"] == 1

    assert [%{"status" => "completed", "attempts" => 1, "result" => %{"attempts" => 2}}] =
             root |> Outbox.current() |> Map.values()
  end

  test "commits workspace changes for git commit effects" do
    root = tmp_dir()
    repo = git_repo!()
    File.write!(Path.join(repo, "change.txt"), "change\n")

    effect =
      Effect.new("git.commit_workspace", "node_run", "node-1", %{
        "workspace_path" => repo,
        "message" => "Indexer checkpoint"
      })

    Outbox.record_pending!(root, effect)

    assert {:ok, result} = Executor.drain(root)
    assert result["completed"] == 1

    assert [%{"status" => "completed", "result" => %{"status" => "committed"}}] =
             root |> Outbox.current() |> Map.values()

    assert git!(repo, ["status", "--porcelain"]) == ""
    assert git!(repo, ["log", "-1", "--pretty=%s"]) == "Indexer checkpoint"
  end

  defp tmp_dir do
    path =
      Path.join(
        System.tmp_dir!(),
        "indexer-effect-executor-test-#{System.unique_integer([:positive])}"
      )

    File.rm_rf!(path)
    File.mkdir_p!(path)
    path
  end

  defp git_repo! do
    path =
      Path.join(
        System.tmp_dir!(),
        "indexer-effect-git-test-#{System.unique_integer([:positive])}"
      )

    File.rm_rf!(path)
    File.mkdir_p!(path)
    git!(path, ["init", "-b", "main"])
    path
  end

  defp git!(repo, args) do
    {stdout, exit_code} = System.cmd("git", args, cd: repo, stderr_to_stdout: true)
    assert exit_code == 0, stdout
    String.trim(stdout)
  end
end
