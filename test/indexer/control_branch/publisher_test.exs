defmodule Indexer.ControlBranch.PublisherTest do
  use ExUnit.Case, async: true

  alias Indexer.ControlBranch.Publisher

  test "publishes control snapshot to a git worktree branch" do
    repo = git_repo!()
    commit_file!(repo, "README.md", "# Repo\n", "initial")
    Indexer.WorkItems.create!(repo, %{id: "TASK-001", title: "Publish me"})

    assert {:ok, result} = Publisher.publish!(repo)
    assert result["status"] == "committed"
    assert is_binary(result["commit_sha"])

    control_dir = Path.join(repo, ".indexer/control")
    assert File.exists?(Path.join(control_dir, "work_items/TASK-001.json"))
    assert git!(control_dir, ["branch", "--show-current"]) == Indexer.control_branch()

    assert {:ok, unchanged} = Publisher.publish!(repo)
    assert unchanged["status"] == "unchanged"
    assert unchanged["commit_sha"] == result["commit_sha"]
  end

  test "returns an error when control path is occupied by a plain directory" do
    repo = git_repo!()
    commit_file!(repo, "README.md", "# Repo\n", "initial")
    File.mkdir_p!(Path.join(repo, ".indexer/control"))
    File.write!(Path.join(repo, ".indexer/control/not-a-worktree"), "occupied")

    assert {:error, error} = Publisher.publish!(repo)
    assert error["reason"] == "control_worktree_path_not_empty"
  end

  defp git_repo! do
    path =
      Path.join(
        System.tmp_dir!(),
        "indexer-control-publish-test-#{System.unique_integer([:positive])}"
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
