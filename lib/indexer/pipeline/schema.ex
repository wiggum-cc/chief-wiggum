defmodule Indexer.Pipeline.Schema do
  @moduledoc """
  Validator for the v2 ordered-step pipeline schema.
  """

  @reserved_jumps MapSet.new(["self", "prev", "next", "abort"])

  @type error :: %{path: String.t(), message: String.t()}

  @doc """
  Validates a pipeline map.
  """
  @spec validate(map()) :: :ok | {:error, [error()]}
  def validate(pipeline) when is_map(pipeline) do
    normalized = Indexer.State.Json.normalize(pipeline)
    errors = root_errors(normalized) ++ step_errors(normalized)

    case errors do
      [] -> :ok
      errors -> {:error, errors}
    end
  end

  def validate(_), do: {:error, [error("$", "pipeline must be an object")]}

  @doc """
  Validates a pipeline and raises on errors.
  """
  @spec validate!(map()) :: :ok
  def validate!(pipeline) do
    case validate(pipeline) do
      :ok ->
        :ok

      {:error, errors} ->
        formatted = Enum.map_join(errors, "\n", &"#{&1.path}: #{&1.message}")
        raise ArgumentError, "invalid pipeline:\n#{formatted}"
    end
  end

  defp root_errors(%{"name" => name, "steps" => steps}) do
    []
    |> require_binary("$.name", name)
    |> require_non_empty_list("$.steps", steps)
  end

  defp root_errors(%{} = pipeline) do
    []
    |> maybe_missing(pipeline, "name", "$.name is required")
    |> maybe_missing(pipeline, "steps", "$.steps is required")
  end

  defp step_errors(%{"steps" => steps}) when is_list(steps) do
    ids = step_ids(steps)
    duplicate_ids = duplicates(ids)
    id_set = MapSet.new(ids)

    steps
    |> Enum.with_index()
    |> Enum.flat_map(fn {step, index} -> validate_step(step, "$.steps[#{index}]", id_set) end)
    |> Kernel.++(Enum.map(duplicate_ids, &error("$.steps", "duplicate step id #{inspect(&1)}")))
  end

  defp step_errors(_pipeline), do: []

  defp validate_step(step, path, id_set) when is_map(step) do
    []
    |> require_binary("#{path}.id", Map.get(step, "id"))
    |> require_binary("#{path}.agent", Map.get(step, "agent"))
    |> validate_non_negative_integer("#{path}.max", Map.get(step, "max"))
    |> validate_non_negative_integer("#{path}.timeout_seconds", Map.get(step, "timeout_seconds"))
    |> validate_jump("#{path}.on_max", Map.get(step, "on_max", "next"), id_set)
    |> Kernel.++(validate_handlers(Map.get(step, "on_result", %{}), "#{path}.on_result", id_set))
  end

  defp validate_step(_step, path, _id_set), do: [error(path, "step must be an object")]

  defp validate_handlers(handlers, path, id_set) when is_map(handlers) do
    Enum.flat_map(handlers, fn {result, handler} ->
      handler_path = "#{path}.#{result}"
      validate_handler(handler, handler_path, id_set)
    end)
  end

  defp validate_handlers(nil, _path, _id_set), do: []

  defp validate_handlers(_handlers, path, _id_set),
    do: [error(path, "on_result must be an object")]

  defp validate_handler(%{"jump" => jump}, path, id_set) do
    validate_jump([], "#{path}.jump", jump, id_set)
  end

  defp validate_handler(%{"agent" => _agent} = handler, path, id_set) do
    []
    |> require_binary("#{path}.id", Map.get(handler, "id"))
    |> require_binary("#{path}.agent", Map.get(handler, "agent"))
    |> validate_non_negative_integer("#{path}.max", Map.get(handler, "max"))
    |> validate_non_negative_integer(
      "#{path}.timeout_seconds",
      Map.get(handler, "timeout_seconds")
    )
    |> validate_jump("#{path}.on_max", Map.get(handler, "on_max", "next"), id_set)
    |> Kernel.++(
      validate_handlers(Map.get(handler, "on_result", %{}), "#{path}.on_result", id_set)
    )
  end

  defp validate_handler(_handler, path, _id_set) do
    [error(path, "handler must be a jump handler or inline agent handler")]
  end

  defp validate_jump(errors, _path, nil, _id_set), do: errors

  defp validate_jump(errors, path, jump, id_set) when is_binary(jump) do
    if MapSet.member?(@reserved_jumps, jump) or MapSet.member?(id_set, jump) do
      errors
    else
      [error(path, "unknown jump target #{inspect(jump)}") | errors]
    end
  end

  defp validate_jump(errors, path, _jump, _id_set),
    do: [error(path, "jump target must be a string") | errors]

  defp validate_non_negative_integer(errors, _path, nil), do: errors

  defp validate_non_negative_integer(errors, _path, value)
       when is_integer(value) and value >= 0 do
    errors
  end

  defp validate_non_negative_integer(errors, path, _value) do
    [error(path, "must be a non-negative integer") | errors]
  end

  defp require_binary(errors, _path, value) when is_binary(value) and value != "", do: errors

  defp require_binary(errors, path, _value),
    do: [error(path, "must be a non-empty string") | errors]

  defp require_non_empty_list(errors, _path, value) when is_list(value) and value != [],
    do: errors

  defp require_non_empty_list(errors, path, _value),
    do: [error(path, "must be a non-empty list") | errors]

  defp maybe_missing(errors, map, key, message) do
    if Map.has_key?(map, key), do: errors, else: [error("$", message) | errors]
  end

  defp step_ids(steps) do
    steps
    |> Enum.filter(&is_map/1)
    |> Enum.map(&Map.get(&1, "id"))
    |> Enum.filter(&is_binary/1)
  end

  defp duplicates(values) do
    values
    |> Enum.frequencies()
    |> Enum.filter(fn {_value, count} -> count > 1 end)
    |> Enum.map(fn {value, _count} -> value end)
  end

  defp error(path, message), do: %{path: path, message: message}
end
