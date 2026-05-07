defmodule Indexer.Config do
  @moduledoc """
  Configuration file helpers.
  """

  @doc """
  Reads and decodes a JSON config file.
  """
  @spec read_json!(Path.t()) :: map()
  def read_json!(path) when is_binary(path) do
    path
    |> File.read!()
    |> JSON.decode!()
  end
end
