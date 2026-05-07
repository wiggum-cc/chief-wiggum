defmodule Indexer.Effects.Outbox do
  @moduledoc """
  JSONL-backed effect outbox helpers.

  The runner/executor is not implemented yet. This module starts the durable
  record protocol required by the specs and TLA model.
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
end
