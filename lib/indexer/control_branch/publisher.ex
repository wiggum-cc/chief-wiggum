defmodule Indexer.ControlBranch.Publisher do
  @moduledoc """
  Publishes control snapshots into a git worktree for the control branch.

  This helper never checks out the control branch in the project worktree. It
  creates or reuses `.indexer/control` as a separate git worktree and commits the
  exported records there.
  """

  alias Indexer.Git.Repository
  alias Indexer.State.{Event, Jsonl}

  @doc """
  Exports current state to the control-branch worktree and commits changes.
  """
  @spec publish!(Path.t(), keyword()) :: {:ok, map()} | {:error, map()}
  def publish!(project_root, opts \\ []) when is_binary(project_root) do
    branch = Keyword.get(opts, :branch, Indexer.control_branch())

    worktree_path =
      Keyword.get(opts, :worktree_path, Path.join(Indexer.state_dir(project_root), "control"))

    with :ok <- ensure_repository(project_root),
         :ok <- ensure_worktree(project_root, worktree_path, branch) do
      prune_export_dirs!(worktree_path)
      export = Indexer.ControlBranch.Exporter.export!(project_root, output_dir: worktree_path)

      case commit_if_changed(worktree_path, Keyword.get(opts, :message, default_message())) do
        {:ok, result} ->
          payload = Map.merge(export, result) |> Map.put("branch", branch)
          append_sync_event!(project_root, "control_sync.published", payload, opts)
          {:ok, payload}

        {:error, error} ->
          append_sync_event!(project_root, "control_sync.publish_failed", error, opts)
          {:error, error}
      end
    end
  end

  defp ensure_repository(project_root) do
    if Repository.repo?(project_root),
      do: :ok,
      else: {:error, %{"reason" => "not_git_repository"}}
  end

  defp ensure_worktree(project_root, worktree_path, branch) do
    cond do
      control_checkout?(worktree_path) ->
        :ok

      File.exists?(worktree_path) and File.ls!(worktree_path) != [] ->
        {:error, %{"reason" => "control_worktree_path_not_empty", "path" => worktree_path}}

      branch_exists?(project_root, branch) ->
        File.mkdir_p!(Path.dirname(worktree_path))

        project_root
        |> Repository.git(["worktree", "add", worktree_path, branch])
        |> ok_or_error()

      true ->
        File.mkdir_p!(Path.dirname(worktree_path))

        project_root
        |> Repository.git(["worktree", "add", "-b", branch, worktree_path, "HEAD"])
        |> ok_or_error()
    end
  end

  defp control_checkout?(worktree_path) do
    git_path = Path.join(worktree_path, ".git")
    File.dir?(git_path) or File.regular?(git_path)
  end

  defp branch_exists?(project_root, branch) do
    match?({:ok, _sha}, Repository.rev_parse(project_root, "refs/heads/#{branch}"))
  end

  defp ok_or_error({:ok, _output}), do: :ok
  defp ok_or_error({:error, error}), do: {:error, error}

  defp prune_export_dirs!(worktree_path) do
    Enum.each(
      ["work_items", "change_sets", "reviews", "runs", "snapshots", "state"],
      fn dirname ->
        File.rm_rf!(Path.join(worktree_path, dirname))
      end
    )
  end

  defp commit_if_changed(worktree_path, message) do
    with {:ok, _add} <- Repository.git(worktree_path, ["add", "-A"]),
         {:ok, status} <- Repository.git(worktree_path, ["status", "--porcelain"]) do
      if status == "" do
        {:ok, %{"status" => "unchanged", "commit_sha" => current_head(worktree_path)}}
      else
        with {:ok, _commit} <- Repository.git(worktree_path, ["commit", "-m", message]),
             {:ok, sha} <- Repository.rev_parse(worktree_path, "HEAD") do
          {:ok, %{"status" => "committed", "commit_sha" => sha}}
        end
      end
    end
  end

  defp current_head(worktree_path) do
    case Repository.rev_parse(worktree_path, "HEAD") do
      {:ok, sha} -> sha
      {:error, _} -> nil
    end
  end

  defp append_sync_event!(project_root, type, payload, opts) do
    event =
      Event.new(
        "control_sync",
        type,
        "control:#{Keyword.get(opts, :branch, Indexer.control_branch())}",
        payload,
        actor: Keyword.get(opts, :actor, %{"type" => "control-branch", "id" => "publisher"}),
        correlation_id: Keyword.get(opts, :correlation_id)
      )

    Jsonl.append_event!(project_root, event)
  end

  defp default_message do
    "Update Indexer control snapshot"
  end
end
