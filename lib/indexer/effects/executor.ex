defmodule Indexer.Effects.Executor do
  @moduledoc """
  Idempotent effect outbox executor.

  This module executes deterministic state effects. Git effects are recorded with
  enough structure to be picked up by a stricter git executor later; the core
  state mutations already route through the outbox boundary.
  """

  alias Indexer.Effects.{Effect, Outbox}

  @doc """
  Drains pending effects once.
  """
  @spec drain(Path.t(), keyword()) :: {:ok, map()}
  def drain(project_root, opts \\ []) when is_binary(project_root) do
    max_attempts = Keyword.get(opts, :max_attempts, 1)
    effects = Outbox.ready(project_root, max_attempts)

    results =
      Enum.map(effects, fn effect_map ->
        effect = to_effect(effect_map)
        execute_one(project_root, effect, opts)
      end)

    {:ok,
     %{
       "attempted" => length(results),
       "completed" => Enum.count(results, &match?({:ok, _}, &1)),
       "retries" => Enum.count(results, &match?({:retry, _}, &1)),
       "failed" => Enum.count(results, &match?({:error, _}, &1)),
       "results" => Enum.map(results, &normalize_result/1)
     }}
  end

  @doc """
  Executes one effect and records completion/failure.
  """
  @spec execute_one(Path.t(), Effect.t(), keyword()) ::
          {:ok, map()} | {:retry, map()} | {:error, map()}
  def execute_one(project_root, %Effect{} = effect, opts \\ []) do
    runner = Keyword.get(opts, :runner, &dispatch/2)
    max_attempts = Keyword.get(opts, :max_attempts, 1)

    case runner.(project_root, effect) do
      {:ok, result} ->
        Outbox.mark_completed!(project_root, effect, result)
        {:ok, result}

      {:error, error} ->
        error = normalize_error(error)

        if effect.attempts + 1 < max_attempts do
          Outbox.mark_retry!(project_root, effect, error)
          {:retry, error}
        else
          Outbox.mark_failed!(project_root, effect, error)
          {:error, error}
        end
    end
  rescue
    exception ->
      error = %{
        "reason" => Exception.message(exception),
        "class" => inspect(exception.__struct__)
      }

      if effect.attempts + 1 < Keyword.get(opts, :max_attempts, 1) do
        Outbox.mark_retry!(project_root, effect, error)
        {:retry, error}
      else
        Outbox.mark_failed!(project_root, effect, error)
        {:error, error}
      end
  end

  defp dispatch(project_root, %Effect{effect_type: "work_item.create", payload: payload}) do
    {:ok, %{"work_item" => Indexer.WorkItems.create!(project_root, payload)}}
  end

  defp dispatch(project_root, %Effect{
         effect_type: "work_item.status",
         scope_id: work_item_id,
         payload: payload
       }) do
    status = Map.fetch!(payload, "status")
    {:ok, %{"work_item" => Indexer.WorkItems.update_status!(project_root, work_item_id, status)}}
  end

  defp dispatch(project_root, %Effect{effect_type: "worker.spawn", payload: payload}) do
    {:ok, %{"worker" => Indexer.Workers.spawn!(project_root, payload)}}
  end

  defp dispatch(project_root, %Effect{effect_type: "git.prepare_worker", scope_id: worker_id}) do
    with {:ok, worker} <- Indexer.Workers.get(project_root, worker_id),
         {:ok, result} <- Indexer.Git.Worktree.prepare_worker(project_root, worker) do
      Indexer.Workers.update!(project_root, worker_id, %{
        "workspace_path" => result["workspace_path"],
        "work_branch" => result["work_branch"],
        "worktree_status" => result["status"]
      })

      {:ok, Map.put(result, "worker_id", worker_id)}
    end
  end

  defp dispatch(project_root, %Effect{effect_type: "git.commit_workspace", payload: payload}) do
    payload = Indexer.State.Json.normalize(payload)
    workspace = Map.get(payload, "workspace_path", project_root)
    message = Map.get(payload, "message", "Indexer checkpoint")

    cond do
      not Indexer.Git.Repository.repo?(workspace) ->
        {:error, %{"reason" => "not_git_repository", "workspace_path" => workspace}}

      true ->
        commit_workspace(workspace, message)
    end
  end

  defp dispatch(project_root, %Effect{effect_type: "change_set.create", payload: payload}) do
    {:ok, %{"change_set" => Indexer.ChangeSets.create!(project_root, payload)}}
  end

  defp dispatch(project_root, %Effect{effect_type: "control_branch.publish", payload: payload}) do
    opts =
      payload
      |> Indexer.State.Json.normalize()
      |> Enum.map(fn
        {"branch", branch} -> {:branch, branch}
        {"message", message} -> {:message, message}
        {"worktree_path", path} -> {:worktree_path, path}
        {key, value} -> {String.to_atom(key), value}
      end)

    case Indexer.ControlBranch.Publisher.publish!(project_root, opts) do
      {:ok, result} -> {:ok, result}
      {:error, error} -> {:error, error}
    end
  end

  defp dispatch(project_root, %Effect{effect_type: "control_branch.import", payload: payload}) do
    opts =
      payload
      |> Indexer.State.Json.normalize()
      |> Enum.map(fn
        {"branch", branch} -> {:branch, branch}
        {"input_dir", path} -> {:input_dir, path}
        {key, value} -> {String.to_atom(key), value}
      end)

    {:ok, Indexer.ControlBranch.Importer.import!(project_root, opts)}
  end

  defp dispatch(project_root, %Effect{
         effect_type: "git.merge_change_set",
         scope_id: change_set_id
       }) do
    with {:ok, change_set} <- Indexer.ChangeSets.get(project_root, change_set_id) do
      Indexer.ChangeSets.update_status!(project_root, change_set_id, "merging")

      case Indexer.Git.MergeExecutor.merge_change_set(project_root, change_set) do
        {:ok, %{"status" => "already_merged"} = result} ->
          Indexer.ChangeSets.mark_merged!(project_root, change_set_id, result["merge_sha"])

          maybe_transition_worker(
            project_root,
            change_set["worker_id"],
            "merge.already_merged",
            result
          )

          maybe_mark_work_item_merged(project_root, change_set["work_item_id"])
          {:ok, Map.put(result, "change_set_id", change_set_id)}

        {:ok, %{"status" => "merged"} = result} ->
          Indexer.ChangeSets.mark_merged!(project_root, change_set_id, result["merge_sha"])

          maybe_transition_worker(
            project_root,
            change_set["worker_id"],
            "merge.succeeded",
            result
          )

          maybe_mark_work_item_merged(project_root, change_set["work_item_id"])
          {:ok, Map.put(result, "change_set_id", change_set_id)}

        {:error, %{"reason" => "merge_conflict"} = error} ->
          Indexer.ChangeSets.mark_conflict!(project_root, change_set_id, %{
            "files" => error["files"]
          })

          maybe_transition_worker(project_root, change_set["worker_id"], "merge.conflict", error)
          {:error, Map.put(error, "change_set_id", change_set_id)}

        {:error, error} ->
          Indexer.ChangeSets.update_status!(project_root, change_set_id, "failed", %{
            "error" => error
          })

          maybe_transition_worker(project_root, change_set["worker_id"], "merge.hard_fail", error)
          {:error, Map.put(error, "change_set_id", change_set_id)}
      end
    end
  end

  defp dispatch(_project_root, %Effect{effect_type: effect_type}) do
    {:error, %{"reason" => "unsupported_effect", "effect_type" => effect_type}}
  end

  defp to_effect(effect_map) do
    %Effect{
      id: Map.fetch!(effect_map, "id"),
      batch_id: effect_map["batch_id"],
      effect_type: Map.fetch!(effect_map, "effect_type"),
      scope_type: Map.fetch!(effect_map, "scope_type"),
      scope_id: Map.fetch!(effect_map, "scope_id"),
      idempotency_key: Map.fetch!(effect_map, "idempotency_key"),
      payload: Map.get(effect_map, "payload", %{}),
      status: Map.get(effect_map, "status", "pending"),
      attempts: Map.get(effect_map, "attempts", 0)
    }
  end

  defp normalize_result({:ok, result}), do: %{"status" => "completed", "result" => result}
  defp normalize_result({:retry, error}), do: %{"status" => "retry_scheduled", "error" => error}
  defp normalize_result({:error, error}), do: %{"status" => "failed", "error" => error}

  defp normalize_error(error) when is_map(error), do: Indexer.State.Json.normalize(error)
  defp normalize_error(error), do: %{"reason" => inspect(error)}

  defp commit_workspace(workspace, message) do
    with {:ok, status} <-
           Indexer.Git.Repository.git(workspace, [
             "status",
             "--porcelain",
             "--",
             ".",
             ":!.indexer"
           ]) do
      if status == "" do
        {:ok, %{"status" => "no_changes", "workspace_path" => workspace}}
      else
        with {:ok, _} <-
               Indexer.Git.Repository.git(workspace, ["add", "-A", "--", ".", ":!.indexer"]),
             {:ok, _} <-
               Indexer.Git.Repository.git(workspace, [
                 "-c",
                 "user.name=Indexer",
                 "-c",
                 "user.email=indexer@example.invalid",
                 "commit",
                 "-m",
                 message
               ]),
             {:ok, sha} <- Indexer.Git.Repository.rev_parse(workspace, "HEAD") do
          {:ok,
           %{
             "status" => "committed",
             "workspace_path" => workspace,
             "commit_sha" => sha
           }}
        end
      end
    end
  end

  defp maybe_transition_worker(_project_root, nil, _event_type, _payload), do: :ok

  defp maybe_transition_worker(project_root, worker_id, event_type, payload) do
    Indexer.Workers.transition!(project_root, worker_id, event_type, payload)
    :ok
  rescue
    _exception -> :ok
  end

  defp maybe_mark_work_item_merged(_project_root, nil), do: :ok

  defp maybe_mark_work_item_merged(project_root, work_item_id) do
    Indexer.WorkItems.update_status!(project_root, work_item_id, "merged",
      reason: "change_set_merged"
    )

    :ok
  rescue
    _exception -> :ok
  end
end
