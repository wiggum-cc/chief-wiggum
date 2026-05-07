defmodule Indexer.Runtime.NormalizedEvent do
  @moduledoc """
  Backend-independent runtime event.
  """

  @enforce_keys [:event_type, :agent_run_id, :runtime, :sequence, :payload]
  defstruct [
    :event_type,
    :agent_run_id,
    :runtime,
    :session_id,
    :turn_id,
    :sequence,
    :payload,
    usage: %{},
    raw_ref: nil
  ]

  @type t :: %__MODULE__{}
end
