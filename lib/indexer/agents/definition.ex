defmodule Indexer.Agents.Definition do
  @moduledoc """
  Agent definition validation.

  Markdown parsing and hook loading will build on this normalized definition
  struct.
  """

  @modes MapSet.new(["ralph_loop", "once", "live", "resume"])

  @enforce_keys [:type, :description, :required_paths, :valid_results, :mode]
  defstruct [
    :type,
    :description,
    :required_paths,
    :valid_results,
    :mode,
    readonly: false,
    report_tag: "report",
    result_tag: "result",
    output_path: nil,
    completion_check: "result_tag",
    session_from: nil,
    supervisor_interval: 0,
    plan_file: nil,
    outputs: [],
    runtime: %{},
    hooks: %{},
    capabilities: [],
    artifact_contracts: []
  ]

  @type t :: %__MODULE__{}

  @spec from_map(map()) :: {:ok, t()} | {:error, [map()]}
  def from_map(map) when is_map(map) do
    normalized = Indexer.State.Json.normalize(map)

    definition = %__MODULE__{
      type: Map.get(normalized, "type"),
      description: Map.get(normalized, "description"),
      required_paths: Map.get(normalized, "required_paths", []),
      valid_results: Map.get(normalized, "valid_results", []),
      mode: Map.get(normalized, "mode"),
      readonly: Map.get(normalized, "readonly", false),
      report_tag: Map.get(normalized, "report_tag", "report"),
      result_tag: Map.get(normalized, "result_tag", "result"),
      output_path: Map.get(normalized, "output_path"),
      completion_check: Map.get(normalized, "completion_check", "result_tag"),
      session_from: Map.get(normalized, "session_from"),
      supervisor_interval: Map.get(normalized, "supervisor_interval", 0),
      plan_file: Map.get(normalized, "plan_file"),
      outputs: Map.get(normalized, "outputs", []),
      runtime: Map.get(normalized, "runtime", %{}),
      hooks: Map.get(normalized, "hooks", %{}),
      capabilities: Map.get(normalized, "capabilities", []),
      artifact_contracts: Map.get(normalized, "artifact_contracts", [])
    }

    case validate(definition) do
      :ok -> {:ok, definition}
      {:error, errors} -> {:error, errors}
    end
  end

  @spec validate(t()) :: :ok | {:error, [map()]}
  def validate(%__MODULE__{} = definition) do
    errors =
      []
      |> require_type(definition.type)
      |> require_string("$.description", definition.description)
      |> require_string_list("$.required_paths", definition.required_paths)
      |> require_string_list("$.valid_results", definition.valid_results)
      |> validate_mode(definition.mode)
      |> validate_resume_session(definition.mode, definition.session_from)
      |> validate_non_negative_integer("$.supervisor_interval", definition.supervisor_interval)

    case errors do
      [] -> :ok
      errors -> {:error, errors}
    end
  end

  defp require_type(errors, type) when is_binary(type) do
    if Regex.match?(~r/^[a-z][a-z0-9-]*(\.[a-z0-9-]+)+$/, type) do
      errors
    else
      [error("$.type", "must be a dotted agent type") | errors]
    end
  end

  defp require_type(errors, _type), do: [error("$.type", "must be a dotted agent type") | errors]

  defp require_string(errors, _path, value) when is_binary(value) and value != "", do: errors

  defp require_string(errors, path, _value),
    do: [error(path, "must be a non-empty string") | errors]

  defp require_string_list(errors, path, value) when is_list(value) and value != [] do
    if Enum.all?(value, &(is_binary(&1) and &1 != "")) do
      errors
    else
      [error(path, "must contain only non-empty strings") | errors]
    end
  end

  defp require_string_list(errors, path, _value),
    do: [error(path, "must be a non-empty list") | errors]

  defp validate_mode(errors, mode) when is_binary(mode) do
    if MapSet.member?(@modes, mode),
      do: errors,
      else: [error("$.mode", "unsupported mode #{inspect(mode)}") | errors]
  end

  defp validate_mode(errors, _mode), do: [error("$.mode", "must be a string") | errors]

  defp validate_resume_session(errors, "resume", session_from)
       when is_binary(session_from) and session_from != "" do
    errors
  end

  defp validate_resume_session(errors, "resume", _session_from) do
    [error("$.session_from", "is required for resume mode") | errors]
  end

  defp validate_resume_session(errors, _mode, _session_from), do: errors

  defp validate_non_negative_integer(errors, _path, value) when is_integer(value) and value >= 0,
    do: errors

  defp validate_non_negative_integer(errors, path, _value) do
    [error(path, "must be a non-negative integer") | errors]
  end

  defp error(path, message), do: %{path: path, message: message}
end
