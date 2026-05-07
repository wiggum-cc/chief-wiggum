defmodule Indexer.Runtime.Invocation do
  @moduledoc """
  Normalized input to a runtime adapter.
  """

  @enforce_keys [
    :agent_run_id,
    :agent_type,
    :runtime,
    :mode,
    :workspace_path,
    :objective,
    :policy
  ]
  defstruct [
    :agent_run_id,
    :agent_type,
    :runtime,
    :mode,
    :workspace_path,
    :objective,
    session: %{},
    policy: %{},
    runtime_config: %{},
    context: %{},
    artifacts: []
  ]

  @type t :: %__MODULE__{}
end
