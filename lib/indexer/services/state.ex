defmodule Indexer.Services.State do
  @moduledoc """
  JSONL-backed service state projection.
  """

  alias Indexer.State.Jsonl

  @doc """
  Folds `services.jsonl` into current per-service state.
  """
  @spec current(Path.t()) :: map()
  def current(project_root) when is_binary(project_root) do
    project_root
    |> Jsonl.ledger_path("services")
    |> Jsonl.read!()
    |> Enum.reduce(%{}, &apply_event/2)
  end

  @doc """
  Returns current state for one service.
  """
  @spec get(Path.t(), String.t()) :: map()
  def get(project_root, service_id) when is_binary(project_root) and is_binary(service_id) do
    current(project_root)
    |> Map.get(service_id, default_entry())
  end

  @spec running?(Path.t(), String.t()) :: boolean()
  def running?(project_root, service_id), do: get(project_root, service_id)["status"] == "running"

  defp apply_event(%{"type" => type, "payload" => payload}, acc) do
    service_id = payload["service_id"]

    if is_binary(service_id) do
      entry =
        acc
        |> Map.get(service_id, default_entry())
        |> apply_service_event(type, payload)

      Map.put(acc, service_id, entry)
    else
      acc
    end
  end

  defp apply_event(_event, acc), do: acc

  defp apply_service_event(entry, "service.started", payload) do
    entry
    |> Map.put("status", "running")
    |> Map.put("last_run", payload["started_at"])
    |> Map.put("current_run_id", payload["run_id"])
  end

  defp apply_service_event(entry, "service.completed", payload) do
    status = payload["status"]

    entry
    |> Map.put("status", status)
    |> Map.put("last_completed_at", payload["completed_at"])
    |> Map.put("last_run_id", payload["run_id"])
    |> Map.put("current_run_id", nil)
    |> update_counts(status)
    |> update_metrics(payload)
  end

  defp apply_service_event(entry, "service.skipped", payload) do
    entry
    |> Map.put("status", "skipped")
    |> Map.put("last_skipped_at", payload["skipped_at"])
    |> Map.put("last_skip_reason", payload["reason"])
  end

  defp apply_service_event(entry, "service.queued", payload) do
    queue = Map.get(entry, "queue", [])

    entry
    |> Map.put("status", "queued")
    |> Map.put("queue", queue ++ [Map.take(payload, ["run_id", "queued_at", "reason"])])
  end

  defp apply_service_event(entry, "service.circuit_opened", payload) do
    entry
    |> Map.put("circuit_state", "open")
    |> Map.put("circuit_opened_at", payload["opened_at"])
  end

  defp apply_service_event(entry, "service.circuit_half_opened", payload) do
    entry
    |> Map.put("circuit_state", "half-open")
    |> Map.put("circuit_half_opened_at", payload["opened_at"])
  end

  defp apply_service_event(entry, "service.circuit_closed", payload) do
    entry
    |> Map.put("circuit_state", "closed")
    |> Map.put("circuit_closed_at", payload["closed_at"])
  end

  defp apply_service_event(entry, _type, _payload), do: entry

  defp update_counts(entry, "success") do
    entry
    |> Map.update!("run_count", &(&1 + 1))
    |> Map.put("consecutive_failures", 0)
  end

  defp update_counts(entry, _status) do
    entry
    |> Map.update!("fail_count", &(&1 + 1))
    |> Map.update!("consecutive_failures", &(&1 + 1))
  end

  defp update_metrics(entry, payload) do
    duration_ms = Map.get(payload, "duration_ms", 0)

    metrics =
      entry
      |> Map.get("metrics", %{})
      |> Map.update("total_duration_ms", duration_ms, &(&1 + duration_ms))
      |> Map.put("last_duration_ms", duration_ms)
      |> put_min_duration(duration_ms)
      |> Map.update("max_duration_ms", duration_ms, &max(&1, duration_ms))

    Map.put(entry, "metrics", metrics)
  end

  defp put_min_duration(metrics, 0), do: Map.put_new(metrics, "min_duration_ms", 0)

  defp put_min_duration(metrics, duration_ms) do
    case Map.get(metrics, "min_duration_ms", 0) do
      0 -> Map.put(metrics, "min_duration_ms", duration_ms)
      value -> Map.put(metrics, "min_duration_ms", min(value, duration_ms))
    end
  end

  defp default_entry do
    %{
      "status" => "stopped",
      "run_count" => 0,
      "fail_count" => 0,
      "consecutive_failures" => 0,
      "circuit_state" => "closed",
      "queue" => [],
      "metrics" => %{
        "total_duration_ms" => 0,
        "last_duration_ms" => 0,
        "min_duration_ms" => 0,
        "max_duration_ms" => 0
      }
    }
  end
end
