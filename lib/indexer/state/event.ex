defmodule Indexer.State.Event do
  @moduledoc """
  Canonical JSONL event envelope.

  Every durable state transition is represented as one JSON object per line in a
  stream-specific ledger.
  """

  @enforce_keys [
    :id,
    :stream,
    :aggregate_id,
    :type,
    :schema_version,
    :timestamp,
    :actor,
    :payload
  ]
  defstruct [
    :id,
    :stream,
    :aggregate_id,
    :type,
    :schema_version,
    :timestamp,
    :actor,
    :causation_id,
    :correlation_id,
    :payload
  ]

  @type actor :: %{required(String.t()) => String.t()}
  @type t :: %__MODULE__{
          id: String.t(),
          stream: String.t(),
          aggregate_id: String.t(),
          type: String.t(),
          schema_version: pos_integer(),
          timestamp: String.t(),
          actor: actor(),
          causation_id: String.t() | nil,
          correlation_id: String.t() | nil,
          payload: map()
        }

  @doc """
  Builds a new event envelope.
  """
  @spec new(String.t(), String.t(), String.t(), map(), keyword()) :: t()
  def new(stream, type, aggregate_id, payload, opts \\ [])
      when is_binary(stream) and is_binary(type) and is_binary(aggregate_id) and is_map(payload) do
    %__MODULE__{
      id: Keyword.get_lazy(opts, :id, &new_id/0),
      stream: stream,
      aggregate_id: aggregate_id,
      type: type,
      schema_version: Keyword.get(opts, :schema_version, 1),
      timestamp: Keyword.get_lazy(opts, :timestamp, &timestamp/0),
      actor: normalize_actor(Keyword.get(opts, :actor, %{"type" => "system", "id" => "indexer"})),
      causation_id: Keyword.get(opts, :causation_id),
      correlation_id: Keyword.get(opts, :correlation_id),
      payload: payload
    }
  end

  @doc """
  Converts an event struct to a JSON-safe map with string keys.
  """
  @spec to_map(t()) :: map()
  def to_map(%__MODULE__{} = event) do
    event
    |> Map.from_struct()
    |> Indexer.State.Json.normalize()
  end

  defp normalize_actor(actor) when is_map(actor), do: Indexer.State.Json.normalize(actor)

  defp new_id do
    entropy = Base.encode16(:crypto.strong_rand_bytes(8), case: :lower)
    counter = System.unique_integer([:positive, :monotonic])
    "evt_#{System.system_time(:microsecond)}_#{counter}_#{entropy}"
  end

  defp timestamp do
    DateTime.utc_now()
    |> DateTime.truncate(:microsecond)
    |> DateTime.to_iso8601()
  end
end
