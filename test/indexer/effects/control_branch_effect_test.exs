defmodule Indexer.Effects.ControlBranchEffectTest do
  use ExUnit.Case, async: true

  alias Indexer.Effects.{Effect, Executor, Outbox}

  test "control branch publish effect commits exported records" do
    repo = git_repo!()
    commit_file!(repo, "README.md", "# Repo\n", "initial")
    Indexer.WorkItems.create!(repo, %{id: "TASK-001", title: "Publish via effect"})

    effect = Effect.new("control_branch.publish", "control_branch", Indexer.control_branch(), %{})
    Outbox.record_pending!(repo, effect)

    assert {:ok, result} = Executor.drain(repo)
    assert result["completed"] == 1
    assert File.exists?(Path.join(repo, ".indexer/control/work_items/TASK-001.json"))
  end

  defp git_repo! do
    path =
      Path.join(
        System.tmp_dir!(),
        "indexer-control-effect-test-#{System.unique_integer([:positive])}"
      )

    File.rm_rf!(path)
    File.mkdir_p!(path)
    git!(path, ["init", "-b", "main"])
    git!(path, ["config", "user.email", "indexer@example.test"])
    git!(path, ["config", "user.name", "Indexer Test"])
    path
  end

  defp commit_file!(repo, path, contents, message) do
    File.write!(Path.join(repo, path), contents)
    git!(repo, ["add", path])
    git!(repo, ["commit", "-m", message])
  end

  defp git!(repo, args) do
    {stdout, exit_code} = System.cmd("git", args, cd: repo, stderr_to_stdout: true)
    assert exit_code == 0, stdout
    String.trim(stdout)
  end
end
