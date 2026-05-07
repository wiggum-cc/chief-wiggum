defmodule Indexer.ControlBranch.Importer do
  @moduledoc """
  Imports human-reviewable control branch records back into JSONL ledgers.
  """

  alias Indexer.State.{Event, Jsonl}

  @doc """
  Imports work item and change-set JSON records from a control checkout.
  """
  @spec import!(Path.t(), keyword()) :: map()
  def import!(project_root, opts \\ []) when is_binary(project_root) do
    input_dir =
      Keyword.get(opts, :input_dir, Path.join(Indexer.state_dir(project_root), "control"))

    work_items = import_work_items(project_root, input_dir)
    change_sets = import_change_sets(project_root, input_dir)

    payload = %{
      "input_dir" => input_dir,
      "work_items" => length(work_items),
      "change_sets" => length(change_sets),
      "imported" => work_items ++ change_sets,
      "imported_at" => timestamp()
    }

    append_sync_event!(project_root, "control_sync.imported", payload, opts)
    payload
  end

  defp import_work_items(project_root, input_dir) do
    input_dir
    |> Path.join("work_items/*.json")
    |> Path.wildcard()
    |> Enum.map(fn path ->
      item = path |> File.read!() |> JSON.decode!() |> Indexer.State.Json.normalize()

      case Indexer.WorkItems.get(project_root, item["id"]) do
        {:ok, existing} ->
          Indexer.WorkItems.update!(
            project_root,
            item["id"],
            Map.drop(item, ["id", "status", "dependencies"])
          )

          if existing["status"] != item["status"] do
            Indexer.WorkItems.update_status!(project_root, item["id"], item["status"],
              reason: "control_branch_import"
            )
          end

          %{"type" => "work_item", "id" => item["id"], "action" => "updated"}

        {:error, :not_found} ->
          Indexer.WorkItems.create!(project_root, item)
          %{"type" => "work_item", "id" => item["id"], "action" => "created"}
      end
    end)
  end

  defp import_change_sets(project_root, input_dir) do
    input_dir
    |> Path.join("change_sets/*/change_set.json")
    |> Path.wildcard()
    |> Enum.map(fn path ->
      change_set = path |> File.read!() |> JSON.decode!() |> Indexer.State.Json.normalize()

      case Indexer.ChangeSets.get(project_root, change_set["id"]) do
        {:ok, existing} ->
          Indexer.ChangeSets.update!(
            project_root,
            change_set["id"],
            Map.drop(change_set, ["id", "status"])
          )

          if existing["status"] != change_set["status"] do
            Indexer.ChangeSets.update_status!(
              project_root,
              change_set["id"],
              change_set["status"],
              %{
                "reason" => "control_branch_import"
              }
            )
          end

          %{"type" => "change_set", "id" => change_set["id"], "action" => "updated"}

        {:error, :not_found} ->
          Indexer.ChangeSets.create!(project_root, change_set)
          %{"type" => "change_set", "id" => change_set["id"], "action" => "created"}
      end
    end)
  end

  defp append_sync_event!(project_root, type, payload, opts) do
    event =
      Event.new(
        "control_sync",
        type,
        "control:#{Keyword.get(opts, :branch, Indexer.control_branch())}",
        payload,
        actor: Keyword.get(opts, :actor, %{"type" => "control-branch", "id" => "importer"}),
        correlation_id: Keyword.get(opts, :correlation_id)
      )

    Jsonl.append_event!(project_root, event)
  end

  defp timestamp do
    DateTime.utc_now()
    |> DateTime.truncate(:microsecond)
    |> DateTime.to_iso8601()
  end
end
