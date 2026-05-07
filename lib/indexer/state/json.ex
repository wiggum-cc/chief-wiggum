defmodule Indexer.State.Json do
  @moduledoc false

  @doc """
  Converts structs, maps, and keyword-ish input into JSON-safe values.
  """
  def normalize(%_{} = struct), do: struct |> Map.from_struct() |> normalize()

  def normalize(%{} = map) do
    Map.new(map, fn {key, value} -> {normalize_key(key), normalize(value)} end)
  end

  def normalize(list) when is_list(list), do: Enum.map(list, &normalize/1)
  def normalize(%DateTime{} = value), do: DateTime.to_iso8601(value)
  def normalize(%NaiveDateTime{} = value), do: NaiveDateTime.to_iso8601(value)
  def normalize(%Date{} = value), do: Date.to_iso8601(value)
  def normalize(%Time{} = value), do: Time.to_iso8601(value)
  def normalize(value) when is_atom(value), do: Atom.to_string(value)
  def normalize(value), do: value

  defp normalize_key(key) when is_atom(key), do: Atom.to_string(key)
  defp normalize_key(key) when is_binary(key), do: key
  defp normalize_key(key), do: to_string(key)
end
