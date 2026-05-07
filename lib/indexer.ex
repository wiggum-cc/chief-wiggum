defmodule Indexer do
  @moduledoc """
  Public helpers for the Indexer OTP application.

  Indexer is intentionally an orchestrator, not an agent runtime. The modules in
  this application prepare context, persist state, validate workflow definitions,
  and call external runtime adapters.
  """

  @doc """
  Returns the runtime state directory for a target project root.
  """
  @spec state_dir(Path.t()) :: Path.t()
  def state_dir(project_root \\ File.cwd!()) do
    Path.join(project_root, Application.get_env(:indexer, :state_dir_name, ".indexer"))
  end

  @doc """
  Returns the append-only ledger directory for a target project root.
  """
  @spec ledger_dir(Path.t()) :: Path.t()
  def ledger_dir(project_root \\ File.cwd!()) do
    project_root
    |> state_dir()
    |> Path.join("state")
  end

  @doc """
  Returns the configured git control branch.
  """
  @spec control_branch() :: String.t()
  def control_branch do
    Application.get_env(:indexer, :control_branch, "indexer/control")
  end
end
