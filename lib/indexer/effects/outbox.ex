defmodule Indexer.Effects.Outbox do
  @moduledoc """
  JSONL-backed effect outbox helpers.

  The outbox stores pending, retry, completion, and failure records in the
  durable protocol required by the specs and TLA model.
  """

  alias Indexer.Effects.Effect
  alias Indexer.State.Event
  alias Indexer.State.Jsonl

  @stream "effects"

  @doc """
  Records a pending effect.
  """
  @spec record_pending!(Path.t(), Effect.t(), keyword()) :: map()
  def record_pending!(project_root, %Effect{} = effect, opts \\ []) do
    append_effect_event!(project_root, "effect.pending", effect, %{}, opts)
  end

  @doc """
  Folds effect events into the current effect projection.
  """
  @spec current(Path.t()) :: map()
  def current(project_root) when is_binary(project_root) do
    project_root
    |> Jsonl.ledger_path(@stream)
    |> Jsonl.read!()
    |> Enum.reduce(%{}, &fold_effect_event/2)
  end

  @doc """
  Returns pending effects in ledger order.
  """
  @spec pending(Path.t()) :: [map()]
  def pending(project_root) when is_binary(project_root) do
    ready(project_root, :infinity)
  end

  @doc """
  Returns pending effects that still have retry budget.
  """
  @spec ready(Path.t(), pos_integer() | :infinity) :: [map()]
  def ready(project_root, max_attempts) when is_binary(project_root) do
    project_root
    |> current()
    |> Map.values()
    |> Enum.filter(&(&1["status"] == "pending"))
    |> Enum.filter(&within_attempt_budget?(&1, max_attempts))
    |> Enum.sort_by(& &1["id"])
  end

  @doc """
  Marks an effect completed.
  """
  @spec mark_completed!(Path.t(), Effect.t(), map(), keyword()) :: map()
  def mark_completed!(project_root, %Effect{} = effect, result \\ %{}, opts \\ []) do
    append_effect_event!(
      project_root,
      "effect.completed",
      %{effect | status: "completed"},
      result,
      opts
    )
  end

  @doc """
  Marks an effect failed.
  """
  @spec mark_failed!(Path.t(), Effect.t(), map(), keyword()) :: map()
  def mark_failed!(project_root, %Effect{} = effect, error, opts \\ []) when is_map(error) do
    failed = %{effect | status: "failed", attempts: effect.attempts + 1}
    append_effect_event!(project_root, "effect.failed", failed, error, opts)
  end

  @doc """
  Keeps a failed effect pending for a later drain attempt.
  """
  @spec mark_retry!(Path.t(), Effect.t(), map(), keyword()) :: map()
  def mark_retry!(project_root, %Effect{} = effect, error, opts \\ []) when is_map(error) do
    retry = %{effect | status: "pending", attempts: effect.attempts + 1}
    append_effect_event!(project_root, "effect.retry_scheduled", retry, error, opts)
  end

  defp append_effect_event!(project_root, type, effect, extra_payload, opts) do
    payload =
      Map.merge(%{"effect" => Effect.to_map(effect)}, Indexer.State.Json.normalize(extra_payload))

    event =
      Event.new(@stream, type, effect.id, payload,
        actor: Keyword.get(opts, :actor, %{"type" => "service", "id" => "effect-outbox"}),
        causation_id: Keyword.get(opts, :causation_id),
        correlation_id: Keyword.get(opts, :correlation_id)
      )

    Jsonl.append_event!(project_root, event)
  end

  defp fold_effect_event(%{"type" => "effect.pending", "payload" => %{"effect" => effect}}, acc) do
    Map.put(acc, effect["id"], effect)
  end

  defp fold_effect_event(%{"type" => type, "payload" => %{"effect" => effect} = payload}, acc)
       when type in ["effect.completed", "effect.failed", "effect.retry_scheduled"] do
    id = effect["id"]

    Map.update(acc, id, effect, fn existing ->
      existing
      |> Indexer.Agents.Registry.deep_merge(effect)
      |> Map.put("result", Map.drop(payload, ["effect"]))
    end)
  end

  defp fold_effect_event(_event, acc), do: acc

  defp within_attempt_budget?(_effect, :infinity), do: true

  defp within_attempt_budget?(effect, max_attempts) do
    Map.get(effect, "attempts", 0) < max_attempts
  end
end
