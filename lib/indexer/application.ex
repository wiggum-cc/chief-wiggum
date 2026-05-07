defmodule Indexer.Application do
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    children = [
      {Registry, keys: :unique, name: Indexer.Registry},
      {DynamicSupervisor, strategy: :one_for_one, name: Indexer.RuntimeSupervisor}
    ]

    Supervisor.start_link(children, strategy: :one_for_one, name: Indexer.Supervisor)
  end
end
