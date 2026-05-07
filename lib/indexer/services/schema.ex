defmodule Indexer.Services.Schema do
  @moduledoc """
  Validator for service scheduler configuration.
  """

  @id_pattern ~r/^[a-z][a-z0-9_-]*$/
  @phases MapSet.new(["startup", "pre", "periodic", "post", "shutdown"])
  @schedule_types MapSet.new(["interval", "cron", "event", "continuous", "tick"])
  @execution_types MapSet.new(["command", "function", "pipeline", "agent"])

  @type error :: %{path: String.t(), message: String.t()}

  @spec validate(map()) :: :ok | {:error, [error()]}
  def validate(config) when is_map(config) do
    normalized = Indexer.State.Json.normalize(config)
    services = Map.get(normalized, "services")

    errors =
      []
      |> require_string("$.version", Map.get(normalized, "version"))
      |> require_list("$.services", services)
      |> Kernel.++(service_errors(services))
      |> Kernel.++(dependency_errors(services))

    case errors do
      [] -> :ok
      errors -> {:error, errors}
    end
  end

  def validate(_), do: {:error, [error("$", "service config must be an object")]}

  @spec validate!(map()) :: :ok
  def validate!(config) do
    case validate(config) do
      :ok ->
        :ok

      {:error, errors} ->
        formatted = Enum.map_join(errors, "\n", &"#{&1.path}: #{&1.message}")
        raise ArgumentError, "invalid services config:\n#{formatted}"
    end
  end

  defp service_errors(services) when is_list(services) do
    duplicate_errors =
      services
      |> service_ids()
      |> duplicates()
      |> Enum.map(&error("$.services", "duplicate service id #{inspect(&1)}"))

    services
    |> Enum.with_index()
    |> Enum.flat_map(fn {service, index} -> validate_service(service, "$.services[#{index}]") end)
    |> Kernel.++(duplicate_errors)
  end

  defp service_errors(_), do: []

  defp validate_service(service, path) when is_map(service) do
    phase = Map.get(service, "phase", "periodic")

    []
    |> require_service_id("#{path}.id", Map.get(service, "id"))
    |> validate_choice("#{path}.phase", phase, @phases)
    |> validate_schedule_or_triggers(service, path)
    |> validate_execution(Map.get(service, "execution"), "#{path}.execution")
  end

  defp validate_service(_service, path), do: [error(path, "service must be an object")]

  defp validate_schedule_or_triggers(errors, service, path) do
    has_schedule = Map.has_key?(service, "schedule")
    has_triggers = Map.has_key?(service, "triggers")

    errors =
      case {has_schedule, has_triggers} do
        {true, true} -> [error(path, "schedule and triggers are mutually exclusive") | errors]
        {false, false} -> [error(path, "service must define schedule or triggers") | errors]
        _ -> errors
      end

    if has_schedule do
      validate_schedule(errors, Map.get(service, "schedule"), "#{path}.schedule")
    else
      errors
    end
  end

  defp validate_schedule(errors, %{"type" => type} = schedule, path) do
    errors = validate_choice(errors, "#{path}.type", type, @schedule_types)

    case type do
      "interval" ->
        require_non_negative_integer(errors, "#{path}.interval", Map.get(schedule, "interval"))

      "cron" ->
        require_string(errors, "#{path}.cron", Map.get(schedule, "cron"))

      "event" ->
        require_event_trigger(errors, "#{path}.trigger", Map.get(schedule, "trigger"))

      "continuous" ->
        validate_non_negative_integer(
          errors,
          "#{path}.restart_delay",
          Map.get(schedule, "restart_delay")
        )

      "tick" ->
        errors

      _ ->
        errors
    end
  end

  defp validate_schedule(errors, _schedule, path),
    do: [error(path, "schedule must be an object with type") | errors]

  defp validate_execution(errors, %{"type" => type} = execution, path) do
    errors = validate_choice(errors, "#{path}.type", type, @execution_types)

    case type do
      "command" ->
        require_command(errors, "#{path}.command", Map.get(execution, "command"))

      "function" ->
        require_string(errors, "#{path}.module", Map.get(execution, "module"))
        |> require_string("#{path}.function", Map.get(execution, "function"))

      "pipeline" ->
        require_string(errors, "#{path}.pipeline", Map.get(execution, "pipeline"))

      "agent" ->
        require_string(errors, "#{path}.agent", Map.get(execution, "agent"))

      _ ->
        errors
    end
  end

  defp validate_execution(errors, _execution, path),
    do: [error(path, "execution must be an object with type") | errors]

  defp dependency_errors(services) when is_list(services) do
    ids = services |> service_ids() |> MapSet.new()

    services
    |> Enum.filter(&is_map/1)
    |> Enum.flat_map(fn service ->
      service_id = Map.get(service, "id", "<unknown>")

      service
      |> Map.get("depends_on", [])
      |> List.wrap()
      |> Enum.reject(&MapSet.member?(ids, &1))
      |> Enum.map(
        &error("$.services.#{service_id}.depends_on", "unknown dependency #{inspect(&1)}")
      )
    end)
  end

  defp dependency_errors(_), do: []

  defp service_ids(services) do
    services
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

  defp require_service_id(errors, path, value) when is_binary(value) do
    if Regex.match?(@id_pattern, value),
      do: errors,
      else: [error(path, "has invalid service id") | errors]
  end

  defp require_service_id(errors, path, _value),
    do: [error(path, "must be a service id") | errors]

  defp validate_choice(errors, path, value, choices) when is_binary(value) do
    if MapSet.member?(choices, value),
      do: errors,
      else: [error(path, "unsupported value #{inspect(value)}") | errors]
  end

  defp validate_choice(errors, path, _value, _choices),
    do: [error(path, "must be a string") | errors]

  defp require_string(errors, _path, value) when is_binary(value) and value != "", do: errors

  defp require_string(errors, path, _value),
    do: [error(path, "must be a non-empty string") | errors]

  defp require_list(errors, _path, value) when is_list(value), do: errors
  defp require_list(errors, path, _value), do: [error(path, "must be a list") | errors]

  defp require_non_negative_integer(errors, _path, value) when is_integer(value) and value >= 0,
    do: errors

  defp require_non_negative_integer(errors, path, _value),
    do: [error(path, "must be a non-negative integer") | errors]

  defp validate_non_negative_integer(errors, _path, nil), do: errors

  defp validate_non_negative_integer(errors, path, value),
    do: require_non_negative_integer(errors, path, value)

  defp require_event_trigger(errors, _path, value) when is_binary(value) and value != "",
    do: errors

  defp require_event_trigger(errors, path, value) when is_list(value) and value != [] do
    if Enum.all?(value, &(is_binary(&1) and &1 != "")) do
      errors
    else
      [error(path, "must contain non-empty strings") | errors]
    end
  end

  defp require_event_trigger(errors, path, _value),
    do: [error(path, "must be a trigger string or list") | errors]

  defp require_command(errors, _path, value) when is_binary(value) and value != "", do: errors

  defp require_command(errors, path, value) when is_list(value) and value != [] do
    if Enum.all?(value, &(is_binary(&1) and &1 != "")) do
      errors
    else
      [error(path, "must contain non-empty strings") | errors]
    end
  end

  defp require_command(errors, path, _value),
    do: [error(path, "must be a command string or argv list") | errors]

  defp error(path, message), do: %{path: path, message: message}
end
