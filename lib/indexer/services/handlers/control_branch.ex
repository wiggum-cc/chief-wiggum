defmodule Indexer.Services.Handlers.ControlBranch do
  @moduledoc """
  Default git-native control branch service handlers.
  """

  def sync(envelope), do: export(envelope)

  def publish(envelope) do
    project_root = get_in(envelope, ["context", "project_root"])

    case Indexer.ControlBranch.Publisher.publish!(project_root) do
      {:ok, result} ->
        {:ok,
         %{
           "status" => "ok",
           "handler" => __MODULE__ |> Atom.to_string(),
           "service_id" => get_in(envelope, ["service", "id"]),
           "publish" => result
         }}

      {:error, error} ->
        {:error,
         %{
           "status" => "hard_fail",
           "handler" => __MODULE__ |> Atom.to_string(),
           "service_id" => get_in(envelope, ["service", "id"]),
           "error" => error
         }}
    end
  end

  defp export(envelope) do
    project_root = get_in(envelope, ["context", "project_root"])
    result = Indexer.ControlBranch.Exporter.export!(project_root)

    {:ok,
     %{
       "status" => "ok",
       "handler" => __MODULE__ |> Atom.to_string(),
       "service_id" => get_in(envelope, ["service", "id"]),
       "export" => result
     }}
  end
end
