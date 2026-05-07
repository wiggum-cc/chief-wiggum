defmodule Indexer.Runtime.Session do
  @moduledoc """
  Runtime session metadata normalized across adapters.
  """

  @enforce_keys [:runtime, :mode, :status, :started_at]
  defstruct [
    :runtime,
    :mode,
    :runtime_session_id,
    :current_turn_id,
    :os_pid,
    :status,
    :started_at,
    :last_event_at,
    supports_resume: false
  ]

  @type t :: %__MODULE__{}
end
