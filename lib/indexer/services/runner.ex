defmodule Indexer.Services.Runner do
  @moduledoc """
  Executes a single service and records its lifecycle in `services.jsonl`.
  """

  alias Indexer.Services.{Conditions, State}
  alias Indexer.State.{Event, Jsonl}

  @handler_prefix "Elixir.Indexer.Services.Handlers."

  @type result :: %{
          required(String.t()) => term()
        }

  @doc """
  Runs a service once.
  """
  @spec run(Path.t(), map(), keyword()) :: {:ok, result()} | {:error, term()}
  def run(project_root, service, opts \\ []) when is_binary(project_root) and is_map(service) do
    service = Indexer.State.Json.normalize(service)
    context = run_context(project_root, service, opts)

    cond do
      Map.get(service, "enabled", true) == false ->
        {:ok, skip(project_root, service, "disabled", context)}

      not Conditions.met?(Map.get(service, "condition"), context) ->
        {:ok, skip(project_root, service, "condition_false", context)}

      circuit_blocks_run?(project_root, service) ->
        {:ok, skip(project_root, service, "circuit_open", context)}

      blocked_by_concurrency?(project_root, service) ->
        handle_running(project_root, service, context)

      true ->
        do_run(project_root, service, context, opts)
    end
  end

  defp do_run(project_root, service, context, opts) do
    parent_run_id = new_run_id(service["id"])
    policy = restart_policy(service)

    result =
      run_attempts(project_root, service, context, opts, policy, parent_run_id, 0)

    if result["status"] == "success", do: {:ok, result}, else: {:error, result}
  end

  defp run_attempts(project_root, service, context, opts, policy, parent_run_id, attempt) do
    result = run_attempt(project_root, service, context, opts, parent_run_id, attempt)

    if retry_service?(result, policy, attempt) do
      delay_seconds = retry_delay_seconds(policy, attempt)

      append_service_event(project_root, "service.retry_scheduled", service, %{
        "run_id" => result["run_id"],
        "parent_run_id" => parent_run_id,
        "attempt" => attempt,
        "next_attempt" => attempt + 1,
        "delay_seconds" => delay_seconds,
        "reason" => "restart_policy"
      })

      sleep = Keyword.get(opts, :sleep_fun, &Process.sleep/1)
      sleep.(delay_seconds * 1_000)

      run_attempts(project_root, service, context, opts, policy, parent_run_id, attempt + 1)
    else
      result
    end
  end

  defp run_attempt(project_root, service, context, opts, parent_run_id, attempt) do
    run_id = attempt_run_id(parent_run_id, attempt)
    started_at = timestamp()
    started_mono = System.monotonic_time(:millisecond)

    append_service_event(project_root, "service.started", service, %{
      "run_id" => run_id,
      "parent_run_id" => parent_run_id,
      "attempt" => attempt,
      "started_at" => started_at,
      "effective_config" => service
    })

    execution_result =
      service
      |> Map.fetch!("execution")
      |> execute(project_root, service, context, opts)

    completed_at = timestamp()
    duration_ms = System.monotonic_time(:millisecond) - started_mono

    {status, exit_code, output, errors} = normalize_execution_result(execution_result)

    append_service_event(project_root, "service.completed", service, %{
      "run_id" => run_id,
      "parent_run_id" => parent_run_id,
      "attempt" => attempt,
      "status" => status,
      "exit_code" => exit_code,
      "duration_ms" => duration_ms,
      "started_at" => started_at,
      "completed_at" => completed_at,
      "output" => output,
      "errors" => errors
    })

    maybe_open_circuit(project_root, service, status)

    %{
      "run_id" => run_id,
      "parent_run_id" => parent_run_id,
      "attempt" => attempt,
      "service_id" => service["id"],
      "status" => status,
      "exit_code" => exit_code,
      "duration_ms" => duration_ms,
      "output" => output,
      "errors" => errors
    }
  end

  defp execute(%{"type" => "function"} = execution, project_root, service, context, opts) do
    case Keyword.get(opts, :function_runner) do
      runner when is_function(runner, 4) ->
        runner.(execution, service, context, opts)

      _ ->
        run_function(execution, project_root, service, context)
    end
  end

  defp execute(%{"type" => "command"} = execution, _project_root, _service, context, opts) do
    case Keyword.get(opts, :command_runner) do
      runner when is_function(runner, 3) ->
        runner.(execution, context, opts)

      _ ->
        run_command(execution, context)
    end
  end

  defp execute(%{"type" => "pipeline"} = execution, project_root, service, context, opts) do
    case Keyword.get(opts, :pipeline_runner) do
      runner when is_function(runner, 4) ->
        runner.(project_root, execution, service, context)

      _ ->
        pipeline = Indexer.Pipeline.Loader.load_file!(pipeline_path(project_root, execution))
        agent_runner = Indexer.Agents.Runner.runner(project_root, opts)
        Indexer.Pipeline.Run.run(project_root, pipeline, agent_runner)
    end
  end

  defp execute(%{"type" => "agent"} = execution, project_root, _service, context, opts) do
    agent_type = Map.fetch!(execution, "agent")
    Indexer.Agents.Runner.run(project_root, agent_type, context, opts)
  end

  defp execute(execution, _project_root, _service, _context, _opts),
    do: {:error, {:unsupported_execution, execution}}

  defp retry_service?(%{"status" => "success"}, _policy, _attempt), do: false

  defp retry_service?(_result, %{"on_failure" => "retry", "max_retries" => max_retries}, attempt) do
    attempt < max_retries
  end

  defp retry_service?(_result, _policy, _attempt), do: false

  defp retry_delay_seconds(policy, attempt) do
    backoff = Map.get(policy, "backoff", %{})
    initial = Map.get(backoff, "initial", 5)
    multiplier = Map.get(backoff, "multiplier", 2)
    max_delay = Map.get(backoff, "max", 300)

    initial
    |> multiply_backoff(multiplier, attempt)
    |> min(max_delay)
    |> trunc()
  end

  defp multiply_backoff(initial, _multiplier, 0), do: initial

  defp multiply_backoff(initial, multiplier, attempt) do
    initial * :math.pow(multiplier, attempt)
  end

  defp restart_policy(service) do
    case Map.get(service, "restart_policy", %{}) do
      %{} = policy -> normalize_restart_policy(policy)
      _other -> normalize_restart_policy(%{})
    end
  end

  defp normalize_restart_policy(policy) do
    %{
      "on_failure" => Map.get(policy, "on_failure", "skip"),
      "max_retries" => non_negative_integer(Map.get(policy, "max_retries", 2)),
      "backoff" => normalize_backoff(Map.get(policy, "backoff", %{}))
    }
  end

  defp normalize_backoff(backoff) do
    %{
      "initial" => non_negative_number(Map.get(backoff, "initial", 5)),
      "multiplier" => positive_number(Map.get(backoff, "multiplier", 2)),
      "max" => non_negative_number(Map.get(backoff, "max", 300))
    }
  end

  defp non_negative_integer(value) when is_integer(value) and value >= 0, do: value
  defp non_negative_integer(_value), do: 0

  defp non_negative_number(value) when is_number(value) and value >= 0, do: value
  defp non_negative_number(_value), do: 0

  defp positive_number(value) when is_number(value) and value > 0, do: value
  defp positive_number(_value), do: 1

  defp run_function(execution, _project_root, service, context) do
    with {:ok, module} <- allowlisted_module(Map.get(execution, "module")),
         function when is_binary(function) <- Map.get(execution, "function"),
         function_atom <- String.to_existing_atom(function),
         true <- function_exported?(module, function_atom, 1) || {:error, :unknown_function} do
      envelope = %{
        "service" => service,
        "context" => context,
        "args" => Map.get(execution, "args", [])
      }

      apply(module, function_atom, [envelope])
    else
      nil -> {:error, :missing_function}
      {:error, reason} -> {:error, reason}
      false -> {:error, :unknown_function}
    end
  rescue
    exception -> {:error, {exception.__struct__, Exception.message(exception)}}
  end

  defp run_command(%{"command" => command} = execution, context) do
    timeout = Map.get(execution, "timeout", Map.get(context, "timeout", 300)) * 1_000
    cwd = working_dir(execution, context)

    case normalize_command(command, Map.get(execution, "shell", false)) do
      {:ok, executable, args} ->
        task =
          Task.async(fn ->
            System.cmd(executable, args,
              cd: cwd,
              env: command_env(execution, context),
              stderr_to_stdout: true
            )
          end)

        case Task.yield(task, timeout) || Task.shutdown(task, :brutal_kill) do
          {:ok, {stdout, exit_code}} -> %{exit_code: exit_code, output: %{"stdout" => stdout}}
          nil -> {:error, %{exit_code: 124, errors: [%{"reason" => "timeout"}]}}
        end

      :error ->
        {:error, :invalid_command}
    end
  rescue
    exception -> {:error, {exception.__struct__, Exception.message(exception)}}
  end

  defp blocked_by_concurrency?(project_root, service) do
    concurrency = Map.get(service, "concurrency", %{})
    max_instances = Map.get(concurrency, "max_instances", 1)
    max_instances <= 1 and State.running?(project_root, service["id"])
  end

  defp circuit_blocks_run?(project_root, service) do
    breaker = Map.get(service, "circuit_breaker", %{})

    if Map.get(breaker, "enabled", false) do
      state = State.get(project_root, service["id"])

      state["circuit_state"] == "open" and
        not maybe_half_open_circuit(project_root, service, state, breaker)
    else
      false
    end
  end

  defp maybe_half_open_circuit(project_root, service, state, breaker) do
    cooldown = Map.get(breaker, "cooldown", 300)

    if cooldown_elapsed?(state["circuit_opened_at"], cooldown) do
      append_service_event(project_root, "service.circuit_half_opened", service, %{
        "opened_at" => timestamp(),
        "cooldown" => cooldown
      })

      true
    else
      false
    end
  end

  defp handle_running(project_root, service, context) do
    concurrency = Map.get(service, "concurrency", %{})

    case Map.get(concurrency, "if_running", "skip") do
      "queue" ->
        payload = %{
          "run_id" => new_run_id(service["id"]),
          "queued_at" => timestamp(),
          "reason" => "already_running"
        }

        append_service_event(project_root, "service.queued", service, payload)
        {:ok, Map.merge(%{"service_id" => service["id"], "status" => "queued"}, payload)}

      _ ->
        {:ok, skip(project_root, service, "already_running", context)}
    end
  end

  defp skip(project_root, service, reason, _context) do
    payload = %{
      "run_id" => new_run_id(service["id"]),
      "skipped_at" => timestamp(),
      "reason" => reason
    }

    append_service_event(project_root, "service.skipped", service, payload)
    Map.merge(%{"service_id" => service["id"], "status" => "skipped"}, payload)
  end

  defp maybe_open_circuit(project_root, service, "success"),
    do: maybe_close_circuit(project_root, service)

  defp maybe_open_circuit(project_root, service, _status) do
    breaker = Map.get(service, "circuit_breaker", %{})

    if Map.get(breaker, "enabled", false) do
      threshold = Map.get(breaker, "threshold", 5)
      current = State.get(project_root, service["id"])

      if current["consecutive_failures"] >= threshold do
        append_service_event(project_root, "service.circuit_opened", service, %{
          "opened_at" => timestamp(),
          "threshold" => threshold
        })
      end
    end
  end

  defp maybe_close_circuit(project_root, service) do
    if State.get(project_root, service["id"])["circuit_state"] != "closed" do
      append_service_event(project_root, "service.circuit_closed", service, %{
        "closed_at" => timestamp()
      })
    end
  end

  defp normalize_execution_result({:ok, %{} = output}), do: {"success", 0, output, []}
  defp normalize_execution_result({:ok, output}), do: {"success", 0, %{"result" => output}, []}
  defp normalize_execution_result(:ok), do: {"success", 0, %{}, []}

  defp normalize_execution_result(%{exit_code: 0, output: output}),
    do: {"success", 0, output, []}

  defp normalize_execution_result(%{exit_code: exit_code, output: output})
       when is_integer(exit_code),
       do: {"failure", exit_code, output, []}

  defp normalize_execution_result({:error, %{exit_code: exit_code, errors: errors}})
       when is_integer(exit_code),
       do: {"failure", exit_code, %{}, errors}

  defp normalize_execution_result({:error, reason}),
    do: {"failure", 1, %{}, [%{"reason" => inspect(reason)}]}

  defp normalize_execution_result(other), do: {"success", 0, %{"result" => other}, []}

  defp allowlisted_module(module_name) when is_binary(module_name) do
    module = Module.concat([module_name])

    cond do
      not String.starts_with?(Atom.to_string(module), @handler_prefix) ->
        {:error, :module_not_allowlisted}

      match?({:module, ^module}, Code.ensure_loaded(module)) ->
        {:ok, module}

      true ->
        {:error, :module_not_loaded}
    end
  end

  defp allowlisted_module(_module_name), do: {:error, :invalid_module}

  defp normalize_command(command, false) when is_list(command) and command != [] do
    [executable | args] = command
    {:ok, executable, args}
  end

  defp normalize_command(command, true) when is_binary(command) and command != "" do
    {:ok, "sh", ["-c", command]}
  end

  defp normalize_command(_command, _shell?), do: :error

  defp working_dir(execution, context) do
    execution
    |> Map.get("working_dir", "{{project_root}}")
    |> String.replace("{{project_root}}", Map.get(context, "project_root"))
    |> String.replace("{{project_dir}}", Map.get(context, "project_root"))
  end

  defp command_env(execution, context) do
    env =
      context
      |> Map.get("env", %{})
      |> Map.merge(Map.get(execution, "env", %{}))

    Enum.map(env, fn {key, value} -> {to_string(key), to_string(value)} end)
  end

  defp pipeline_path(project_root, execution) do
    name = Map.fetch!(execution, "pipeline")

    cond do
      Path.type(name) == :absolute ->
        name

      Path.extname(name) == ".json" ->
        Path.expand(name, project_root)

      true ->
        Path.expand("config/pipelines/#{name}.json", project_root)
    end
  end

  defp run_context(project_root, service, opts) do
    env =
      opts
      |> Keyword.get(:env, %{})
      |> Map.new(fn {key, value} -> {to_string(key), to_string(value)} end)

    %{
      "project_root" => project_root,
      "indexer_dir" => Indexer.state_dir(project_root),
      "service_id" => service["id"],
      "run_mode" => Keyword.get(opts, :run_mode, System.get_env("INDEXER_RUN_MODE", "default")),
      "timeout" => Map.get(service, "timeout", 300),
      "env" => env
    }
  end

  defp append_service_event(project_root, type, service, payload) do
    payload =
      %{
        "service_id" => service["id"],
        "phase" => Map.get(service, "phase", "periodic")
      }
      |> Map.merge(Indexer.State.Json.normalize(payload))

    event =
      Event.new("services", type, "service:#{service["id"]}", payload,
        actor: %{"type" => "service-runner", "id" => service["id"]},
        correlation_id: payload["run_id"]
      )

    Jsonl.append_event!(project_root, event)
  end

  defp timestamp do
    DateTime.utc_now()
    |> DateTime.truncate(:microsecond)
    |> DateTime.to_iso8601()
  end

  defp cooldown_elapsed?(nil, _cooldown), do: false

  defp cooldown_elapsed?(opened_at, cooldown) do
    with {:ok, opened, _} <- DateTime.from_iso8601(opened_at) do
      DateTime.diff(DateTime.utc_now(), opened, :second) >= cooldown
    else
      _error -> false
    end
  end

  defp new_run_id(service_id) do
    "service_run_#{service_id}_#{System.unique_integer([:positive, :monotonic])}"
  end

  defp attempt_run_id(parent_run_id, 0), do: parent_run_id
  defp attempt_run_id(parent_run_id, attempt), do: "#{parent_run_id}_retry_#{attempt}"
end
