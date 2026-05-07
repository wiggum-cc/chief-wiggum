defmodule Indexer.Effects.Effect do
  @moduledoc """
  Durable side-effect request.
  """

  @enforce_keys [:id, :effect_type, :scope_type, :scope_id, :idempotency_key, :payload]
  defstruct [
    :id,
    :batch_id,
    :effect_type,
    :scope_type,
    :scope_id,
    :idempotency_key,
    :payload,
    status: "pending",
    attempts: 0
  ]

  @type t :: %__MODULE__{
          id: String.t(),
          batch_id: String.t() | nil,
          effect_type: String.t(),
          scope_type: String.t(),
          scope_id: String.t(),
          idempotency_key: String.t(),
          payload: map(),
          status: String.t(),
          attempts: non_neg_integer()
        }

  @spec new(String.t(), String.t(), String.t(), map(), keyword()) :: t()
  def new(effect_type, scope_type, scope_id, payload, opts \\ [])
      when is_binary(effect_type) and is_binary(scope_type) and is_binary(scope_id) and
             is_map(payload) do
    id = Keyword.get_lazy(opts, :id, &new_id/0)

    %__MODULE__{
      id: id,
      batch_id: Keyword.get(opts, :batch_id),
      effect_type: effect_type,
      scope_type: scope_type,
      scope_id: scope_id,
      idempotency_key:
        Keyword.get(opts, :idempotency_key) ||
          "#{effect_type}:#{scope_type}:#{scope_id}:#{id}",
      payload: payload
    }
  end

  @spec to_map(t()) :: map()
  def to_map(%__MODULE__{} = effect), do: Indexer.State.Json.normalize(effect)

  defp new_id do
    entropy = Base.encode16(:crypto.strong_rand_bytes(8), case: :lower)
    "eff_#{System.system_time(:microsecond)}_#{entropy}"
  end
end
