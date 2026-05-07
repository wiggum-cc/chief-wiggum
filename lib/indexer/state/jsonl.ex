defmodule Indexer.State.Jsonl do
  @moduledoc """
  Append-only JSONL ledger helpers.

  This module intentionally does not keep mutable process state. Projections can
  be rebuilt by replaying ledgers.
  """

  alias Indexer.State.Event

  @type record :: Event.t() | map()

  @doc """
  Returns a stream ledger path under a project root.
  """
  @spec ledger_path(Path.t(), String.t()) :: Path.t()
  def ledger_path(project_root, stream) when is_binary(project_root) and is_binary(stream) do
    project_root
    |> Indexer.ledger_dir()
    |> Path.join("#{stream}.jsonl")
  end

  @doc """
  Appends a record to a JSONL ledger and returns the normalized map.
  """
  @spec append!(Path.t(), record()) :: map()
  def append!(path, %Event{} = event), do: append!(path, Event.to_map(event))

  def append!(path, record) when is_binary(path) and is_map(record) do
    normalized = Indexer.State.Json.normalize(record)
    File.mkdir_p!(Path.dirname(path))
    File.write!(path, JSON.encode!(normalized) <> "\n", [:append])
    normalized
  end

  @doc """
  Reads all complete records from a JSONL ledger.
  """
  @spec read!(Path.t()) :: [map()]
  def read!(path) when is_binary(path) do
    case File.read(path) do
      {:ok, contents} ->
        contents
        |> String.split("\n", trim: true)
        |> Enum.map(&JSON.decode!/1)

      {:error, :enoent} ->
        []
    end
  end

  @doc """
  Appends an event to its named stream under the project root.
  """
  @spec append_event!(Path.t(), Event.t()) :: map()
  def append_event!(project_root, %Event{stream: stream} = event) do
    project_root
    |> ledger_path(stream)
    |> append!(event)
  end

  @doc """
  Truncates a ledger to its last complete newline.

  This is the recovery primitive described by the JSONL specs. It is safe to call
  on missing files.
  """
  @spec recover!(Path.t()) :: :ok
  def recover!(path) when is_binary(path) do
    case File.read(path) do
      {:ok, ""} ->
        :ok

      {:ok, contents} ->
        if String.ends_with?(contents, "\n") do
          :ok
        else
          recovered =
            case :binary.matches(contents, "\n") do
              [] -> ""
              matches -> binary_part(contents, 0, elem(List.last(matches), 0) + 1)
            end

          File.write!(path, recovered)
        end

      {:error, :enoent} ->
        :ok
    end
  end
end
