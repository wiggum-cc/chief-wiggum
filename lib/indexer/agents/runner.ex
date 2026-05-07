defmodule Indexer.Agents.Runner do
  @moduledoc """
  Executes configured agents for pipeline steps.

  The runner owns deterministic orchestration around the external runtime:
  registry resolution, prompt rendering, lifecycle JSONL records, hook execution,
  result extraction, and normalized output returned to the pipeline engine.
  """

  alias Indexer.Agents.{CompletionCheck, Registry, Result}
  alias Indexer.Pipeline.ResultMappings
  alias Indexer.Runtime.Invocation
  alias Indexer.State.{Event, Jsonl}

  @type output :: %{required(String.t()) => term()}

  @doc """
  Returns a two-argument function suitable for `Indexer.Pipeline.Run`.
  """
  @spec runner(Path.t(), keyword()) :: (String.t(), map() -> {:ok, output()} | {:error, term()})
  def runner(project_root, opts \\ []) when is_binary(project_root) do
    fn agent_type, context -> run(project_root, agent_type, context, opts) end
  end

  @doc """
  Runs one agent invocation and returns a pipeline-compatible output map.
  """
  @spec run(Path.t(), String.t(), map(), keyword()) :: {:ok, output()} | {:error, term()}
  def run(project_root, agent_type, context, opts \\ [])
      when is_binary(project_root) and is_binary(agent_type) and is_map(context) do
    context = Indexer.State.Json.normalize(context)
    registry = Keyword.get_lazy(opts, :registry, fn -> load_registry(opts) end)
    overrides = Map.get(context, "config", %{})

    with {:ok, resolved} <- Registry.resolve(registry, agent_type, overrides) do
      execute_resolved(project_root, resolved, context, opts)
    end
  end

  defp load_registry(opts) do
    opts
    |> Keyword.get(:registry_path, default_registry_path())
    |> Registry.from_file!()
  end

  defp default_registry_path do
    Path.expand("config/agents.json", File.cwd!())
  end

  defp execute_resolved(project_root, resolved, context, opts) do
    agent_run_id = new_agent_run_id()
    started_at = timestamp()
    context = Map.put(context, "agent_run_id", agent_run_id)

    append_agent_event(project_root, "agent.started", agent_run_id, %{
      "agent_type" => resolved.type,
      "pipeline_run_id" => context["pipeline_run_id"],
      "node_run_id" => context["node_run_id"],
      "step_id" => context["step_id"],
      "worker_id" => worker_id(context),
      "work_item_id" => work_item_id(context),
      "mode" => resolved.definition.mode,
      "runtime" => resolved.runtime,
      "config" => snapshot_config(resolved)
    })

    case do_execute(project_root, resolved, context, agent_run_id, opts) do
      {:ok, output} ->
        completed_at = timestamp()
        gate_result = get_in(output, ["outputs", "gate_result"])
        mapping = resolve_mapping(gate_result, resolved.result_mappings)

        append_agent_event(project_root, "agent.completed", agent_run_id, %{
          "agent_run_id" => agent_run_id,
          "agent_type" => resolved.type,
          "pipeline_run_id" => context["pipeline_run_id"],
          "node_run_id" => context["node_run_id"],
          "step_id" => context["step_id"],
          "worker_id" => worker_id(context),
          "work_item_id" => work_item_id(context),
          "status" => mapping["status"],
          "exit_code" => mapping["exit_code"],
          "started_at" => started_at,
          "completed_at" => completed_at,
          "duration_seconds" => duration_seconds(started_at, completed_at),
          "outputs" => output["outputs"],
          "artifacts" => output["artifacts"],
          "effects" => output["effects"],
          "errors" => output["errors"],
          "metadata" => output["metadata"]
        })

        {:ok, output}

      {:error, reason} ->
        append_agent_event(project_root, "agent.failed", agent_run_id, %{
          "agent_run_id" => agent_run_id,
          "agent_type" => resolved.type,
          "pipeline_run_id" => context["pipeline_run_id"],
          "node_run_id" => context["node_run_id"],
          "step_id" => context["step_id"],
          "worker_id" => worker_id(context),
          "work_item_id" => work_item_id(context),
          "status" => "failure",
          "exit_code" => 5,
          "started_at" => started_at,
          "completed_at" => timestamp(),
          "outputs" => %{"gate_result" => "UNKNOWN"},
          "artifacts" => [],
          "effects" => [],
          "errors" => [%{"reason" => inspect(reason)}],
          "metadata" => %{}
        })

        {:error, reason}
    end
  end

  defp do_execute(project_root, resolved, context, agent_run_id, opts) do
    hook_runner = Keyword.get(opts, :hook_runner, &Indexer.Hooks.Executor.run/2)

    try do
      with :ok <- validate_required_paths(project_root, resolved.definition, context),
           {:ok, prepared_context, prepared_artifacts} <-
             run_agent_hooks(
               project_root,
               resolved,
               agent_run_id,
               "prepare",
               context,
               hook_runner
             ),
           {:ok, checked_context, checked_artifacts} <-
             run_agent_hooks(
               project_root,
               resolved,
               agent_run_id,
               "before_turn",
               prepared_context,
               hook_runner
             ),
           {:ok, output} <-
             execute_agent_mode(
               project_root,
               resolved,
               checked_context,
               agent_run_id,
               opts,
               hook_runner
             ) do
        {:ok, Map.update!(output, "artifacts", &(prepared_artifacts ++ checked_artifacts ++ &1))}
      end
    after
      run_agent_hooks(project_root, resolved, agent_run_id, "cleanup", context, hook_runner)
    end
  end

  defp execute_agent_mode(project_root, resolved, context, agent_run_id, opts, hook_runner) do
    case resolved.definition.mode do
      "ralph_loop" ->
        execute_ralph_loop(project_root, resolved, context, agent_run_id, opts, hook_runner)

      _other ->
        execute_turn(project_root, resolved, context, agent_run_id, opts, hook_runner, nil)
    end
  end

  defp execute_ralph_loop(project_root, resolved, context, agent_run_id, opts, hook_runner) do
    max_iterations = max_iterations(resolved, context)

    Enum.reduce_while(0..(max_iterations - 1), {:ok, nil, context, []}, fn iteration,
                                                                           {:ok, previous_output,
                                                                            loop_context,
                                                                            artifacts} ->
      turn_context = iteration_context(loop_context, iteration)

      case completion_decision(
             project_root,
             resolved,
             agent_run_id,
             turn_context,
             hook_runner,
             iteration,
             max_iterations,
             artifacts,
             previous_output
           ) do
        {:halt, output} ->
          {:halt, {:ok, output}}

        {:cont, artifacts} ->
          execute_ralph_iteration(
            project_root,
            resolved,
            turn_context,
            agent_run_id,
            opts,
            hook_runner,
            iteration,
            max_iterations,
            artifacts
          )

        {:error, reason} ->
          {:halt, {:error, reason}}
      end
    end)
    |> case do
      {:ok, nil, _context, _artifacts} ->
        {:error, :no_iterations}

      {:ok, output, _context, artifacts} ->
        append_agent_event(project_root, "agent.loop.max_iterations_exceeded", agent_run_id, %{
          "agent_run_id" => agent_run_id,
          "agent_type" => resolved.type,
          "max_iterations" => max_iterations,
          "gate_result" => get_in(output, ["outputs", "gate_result"])
        })

        {:ok,
         output
         |> loop_output(max_iterations, max_iterations, artifacts)
         |> add_loop_error("max_iterations_exceeded", %{"max_iterations" => max_iterations})}

      other ->
        other
    end
  end

  defp execute_ralph_iteration(
         project_root,
         resolved,
         turn_context,
         agent_run_id,
         opts,
         hook_runner,
         iteration,
         max_iterations,
         artifacts
       ) do
    case execute_turn(
           project_root,
           resolved,
           turn_context,
           agent_run_id,
           opts,
           hook_runner,
           iteration
         ) do
      {:ok, output} ->
        gate_result = get_in(output, ["outputs", "gate_result"])
        artifacts = artifacts ++ output["artifacts"]
        output = loop_output(output, iteration + 1, max_iterations, artifacts)

        append_agent_event(project_root, "agent.iteration.completed", agent_run_id, %{
          "agent_run_id" => agent_run_id,
          "agent_type" => resolved.type,
          "iteration" => iteration,
          "gate_result" => gate_result,
          "runtime_session_id" => get_in(output, ["metadata", "runtime_session_id"])
        })

        cond do
          terminal_gate_result?(gate_result, resolved.definition) ->
            {:halt, {:ok, output}}

          true ->
            case completion_decision(
                   project_root,
                   resolved,
                   agent_run_id,
                   turn_context,
                   hook_runner,
                   iteration + 1,
                   max_iterations,
                   artifacts,
                   output
                 ) do
              {:halt, output} ->
                {:halt, {:ok, output}}

              {:cont, artifacts} ->
                case supervisor_decision(
                       project_root,
                       resolved,
                       agent_run_id,
                       next_loop_context(turn_context, output),
                       hook_runner,
                       iteration + 1,
                       max_iterations,
                       artifacts,
                       output
                     ) do
                  {:halt, output} ->
                    {:halt, {:ok, output}}

                  {:cont, output, next_context, artifacts} ->
                    {:cont, {:ok, output, next_context, artifacts}}

                  {:error, reason} ->
                    {:halt, {:error, reason}}
                end

              {:error, reason} ->
                {:halt, {:error, reason}}
            end
        end

      {:error, reason} ->
        {:halt, {:error, reason}}
    end
  end

  defp completion_decision(
         project_root,
         resolved,
         agent_run_id,
         context,
         hook_runner,
         iterations_completed,
         max_iterations,
         artifacts,
         output
       ) do
    with {:ok, check, check_artifacts} <-
           evaluate_completion_check(project_root, resolved, agent_run_id, context, hook_runner) do
      artifacts = artifacts ++ check_artifacts

      if check["complete"] do
        output =
          (output || completion_output(agent_run_id))
          |> apply_completion_check(check, resolved.definition)
          |> loop_output(iterations_completed, max_iterations, artifacts)

        append_agent_event(project_root, "agent.completion_check.completed", agent_run_id, %{
          "agent_run_id" => agent_run_id,
          "agent_type" => resolved.type,
          "iterations_completed" => iterations_completed,
          "completion_check" => check,
          "gate_result" => get_in(output, ["outputs", "gate_result"])
        })

        {:halt, output}
      else
        {:cont, artifacts}
      end
    end
  end

  defp evaluate_completion_check(project_root, resolved, agent_run_id, context, hook_runner) do
    case resolved.definition.completion_check do
      "hook:" <> hook_name ->
        hook_name = String.trim(hook_name)

        with {:ok, checked_context, artifacts} <-
               run_agent_hooks(
                 project_root,
                 resolved,
                 agent_run_id,
                 hook_name,
                 context,
                 hook_runner
               ) do
          gate_result = Map.get(checked_context, "gate_result")

          {:ok,
           %{
             "type" => "hook",
             "hook" => hook_name,
             "complete" =>
               truthy?(Map.get(checked_context, "complete")) ||
                 terminal_gate_result?(gate_result, resolved.definition),
             "gate_result" => gate_result,
             "diagnostics" => Map.get(checked_context, "diagnostics", [])
           }, artifacts}
        end

      _other ->
        {:ok, CompletionCheck.evaluate(project_root, resolved.definition, context), []}
    end
  end

  defp supervisor_decision(
         project_root,
         resolved,
         agent_run_id,
         context,
         hook_runner,
         iterations_completed,
         max_iterations,
         artifacts,
         output
       ) do
    interval = resolved.definition.supervisor_interval

    if interval > 0 and rem(iterations_completed, interval) == 0 do
      with {:ok, supervisor_context, supervisor_artifacts} <-
             run_agent_hooks(
               project_root,
               resolved,
               agent_run_id,
               "supervisor",
               Map.put(context, "output", output),
               hook_runner
             ) do
        artifacts = artifacts ++ supervisor_artifacts
        decision = supervisor_decision_value(supervisor_context)
        feedback = supervisor_feedback(supervisor_context)

        append_agent_event(project_root, "agent.supervisor.completed", agent_run_id, %{
          "agent_run_id" => agent_run_id,
          "agent_type" => resolved.type,
          "iterations_completed" => iterations_completed,
          "decision" => decision,
          "feedback" => feedback
        })

        case decision do
          "STOP" ->
            {:halt,
             output
             |> apply_supervisor_stop(supervisor_context, resolved.definition)
             |> loop_output(iterations_completed, max_iterations, artifacts)}

          "RESTART" ->
            {:cont, output, restart_loop_context(context, feedback), artifacts}

          _continue ->
            {:cont, output, maybe_put(context, "supervisor_feedback", feedback), artifacts}
        end
      end
    else
      {:cont, output, context, artifacts}
    end
  end

  defp execute_turn(project_root, resolved, context, agent_run_id, opts, hook_runner, iteration) do
    objective = render_objective_for_turn(resolved, context, iteration)
    invocation = build_invocation(project_root, resolved, context, objective, agent_run_id)

    with {:ok, runtime_result} <- runtime_invoke(project_root, invocation, opts),
         {:ok, output_context, validation_artifacts} <-
           validate_output(
             project_root,
             resolved,
             agent_run_id,
             runtime_result,
             context,
             hook_runner
           ) do
      text = runtime_result.text

      gate_result =
        Map.get(output_context, "gate_result") ||
          Result.extract_gate_result(text, resolved.definition)

      report = Result.extract_report(text, resolved.definition)

      {:ok,
       %{
         "agent_run_id" => agent_run_id,
         "outputs" => %{
           "gate_result" => gate_result,
           "report" => report,
           "text" => text
         },
         "artifacts" => validation_artifacts,
         "effects" => [],
         "errors" => result_errors(gate_result, resolved.definition.valid_results),
         "metadata" =>
           turn_metadata(invocation, runtime_result)
           |> maybe_put_iteration(iteration)
       }}
    end
  end

  defp runtime_invoke(project_root, invocation, opts) do
    runtime_opts = Keyword.get(opts, :runtime_opts, [])

    case Keyword.get(opts, :runtime_runner) do
      nil -> Indexer.Runtime.invoke(project_root, invocation, runtime_opts)
      runner when is_function(runner, 3) -> runner.(project_root, invocation, runtime_opts)
    end
  end

  defp render_objective_for_turn(resolved, context, nil) do
    objective = render_objective(resolved, context)

    if resolved.definition.mode == "once" do
      Map.put(objective, "continuation", nil)
    else
      objective
    end
  end

  defp render_objective_for_turn(resolved, context, iteration) when is_integer(iteration) do
    objective = render_objective(resolved, context)

    continuation =
      if iteration > 0 do
        objective["continuation"]
      end

    objective
    |> Map.put("continuation", continuation)
    |> maybe_append_continuation(continuation)
  end

  defp render_objective(%{markdown: nil, definition: definition}, context) do
    valid_results = Enum.join(definition.valid_results, ", ")

    %{
      "system" =>
        "You are #{definition.type}. #{definition.description}\nReturn one gate result from: #{valid_results}.",
      "user" => Map.get(context, "objective", "Run pipeline step #{context["step_id"]}."),
      "continuation" => nil,
      "output_schema" => nil
    }
  end

  defp render_objective(%{markdown: markdown}, context) do
    %{
      "system" => Indexer.Agents.Markdown.render(markdown, :system, context),
      "user" => Indexer.Agents.Markdown.render(markdown, :user, context),
      "continuation" => Indexer.Agents.Markdown.render(markdown, :continuation, context),
      "output_schema" => nil
    }
  end

  defp build_invocation(project_root, resolved, context, objective, agent_run_id) do
    runtime = Map.get(resolved.runtime, "adapter", "codex")

    %Invocation{
      agent_run_id: agent_run_id,
      agent_type: resolved.type,
      runtime: runtime,
      mode: Map.get(resolved.runtime, "mode", "cli_text"),
      workspace_path: workspace_path(project_root, context),
      objective: objective,
      session: session_context(resolved, context),
      policy: policy(resolved, context),
      runtime_config: resolved.runtime,
      context: Map.merge(context, %{"agent_type" => resolved.type}),
      artifacts: []
    }
  end

  defp policy(resolved, context) do
    %{
      "approval_policy" =>
        get_in(resolved.config, ["policy", "approval_policy"]) || "unless_trusted",
      "sandbox" => if(resolved.definition.readonly, do: "readonly", else: "workspace_write"),
      "writable_roots" => Map.get(context, "writable_roots", []),
      "network" => Map.get(context, "network", false),
      "timeout_seconds" => resolved.timeout_seconds || 10_800,
      "max_turns" => resolved.max_turns || 50,
      "max_iterations" => resolved.max_iterations || 1
    }
  end

  defp session_context(resolved, context) do
    %{
      "resume" => resolved.definition.mode == "resume",
      "session_from" => resolved.definition.session_from,
      "runtime_session_id" => Map.get(context, "runtime_session_id"),
      "parent_session_id" => get_in(context, ["parent", "session_id"])
    }
  end

  defp validate_output(project_root, resolved, agent_run_id, runtime_result, context, hook_runner) do
    context =
      Map.merge(context, %{
        "runtime" => %{
          "text" => runtime_result.text,
          "session" => Indexer.State.Json.normalize(runtime_result.session),
          "events" => runtime_result.events
        },
        "gate_result" => Result.extract_gate_result(runtime_result.text, resolved.definition)
      })

    run_agent_hooks(project_root, resolved, agent_run_id, "validate_output", context, hook_runner)
  end

  defp run_agent_hooks(project_root, resolved, agent_run_id, hook_name, context, hook_runner) do
    resolved.definition.hooks
    |> Map.get(hook_name, [])
    |> List.wrap()
    |> Enum.reduce_while({:ok, context, []}, fn hook, {:ok, acc_context, acc_artifacts} ->
      envelope = hook_envelope(project_root, resolved, agent_run_id, hook_name, acc_context)

      case hook_runner.(hook, envelope) do
        {:ok, result} ->
          append_agent_event(project_root, "agent.hook.completed", agent_run_id, %{
            "hook" => hook_name,
            "agent_type" => resolved.type,
            "result" => result
          })

          status = Map.get(result, "status", "ok")

          result_context =
            result
            |> Map.take([
              "complete",
              "gate_result",
              "supervisor_decision",
              "supervisor_feedback"
            ])
            |> Map.merge(Map.get(result, "context", %{}))

          next_context = Registry.deep_merge(acc_context, result_context)
          artifacts = acc_artifacts ++ Map.get(result, "artifacts", [])

          if status == "hard_fail" do
            {:halt, {:error, {:hook_failed, hook_name, result}}}
          else
            {:cont, {:ok, next_context, artifacts}}
          end

        {:error, error} ->
          append_agent_event(project_root, "agent.hook.failed", agent_run_id, %{
            "hook" => hook_name,
            "agent_type" => resolved.type,
            "error" => error
          })

          {:halt, {:error, {:hook_failed, hook_name, error}}}
      end
    end)
  end

  defp hook_envelope(project_root, resolved, agent_run_id, hook_name, context) do
    %{
      "hook" => hook_name,
      "agent_id" => resolved.type,
      "agent_run" => %{"id" => agent_run_id},
      "work_item" => Map.get(context, "work_item", %{}),
      "worker" => Map.get(context, "worker", %{}),
      "pipeline_run" => %{"id" => context["pipeline_run_id"]},
      "node_run" => %{"id" => context["node_run_id"], "step_id" => context["step_id"]},
      "workspace" => %{"path" => workspace_path(project_root, context)},
      "repository" => %{"project_root" => project_root},
      "context" => context,
      "artifacts" => [],
      "config" => resolved.config
    }
  end

  defp validate_required_paths(project_root, definition, context) do
    missing =
      definition.required_paths
      |> Enum.map(&resolve_required_path(project_root, context, &1))
      |> Enum.reject(&File.exists?/1)

    case missing do
      [] -> :ok
      paths -> {:error, {:missing_required_paths, paths}}
    end
  end

  defp resolve_required_path(project_root, context, "workspace"),
    do: workspace_path(project_root, context)

  defp resolve_required_path(project_root, _context, "project_dir"), do: project_root
  defp resolve_required_path(project_root, _context, "project_root"), do: project_root

  defp resolve_required_path(project_root, _context, path) do
    if Path.type(path) == :absolute, do: path, else: Path.join(project_root, path)
  end

  defp workspace_path(project_root, context) do
    Map.get(context, "workspace") || Map.get(context, "project_root") || project_root
  end

  defp worker_id(context), do: Map.get(context, "worker_id") || get_in(context, ["worker", "id"])

  defp work_item_id(context) do
    Map.get(context, "work_item_id") || get_in(context, ["work_item", "id"])
  end

  defp resolve_mapping(gate_result, result_mappings) do
    case ResultMappings.resolve(gate_result || "UNKNOWN", result_mappings, %{}) do
      {:ok, mapping} -> mapping
      {:error, :unknown_result} -> %{"status" => "unknown", "exit_code" => 1}
    end
  end

  defp result_errors(gate_result, valid_results) do
    if gate_result in valid_results do
      []
    else
      [%{"reason" => "invalid_gate_result", "gate_result" => gate_result}]
    end
  end

  defp completion_output(agent_run_id) do
    %{
      "agent_run_id" => agent_run_id,
      "outputs" => %{
        "gate_result" => "UNKNOWN",
        "report" => nil,
        "text" => ""
      },
      "artifacts" => [],
      "effects" => [],
      "errors" => [],
      "metadata" => %{}
    }
  end

  defp apply_completion_check(output, check, definition) do
    gate_result =
      check["gate_result"] ||
        get_in(output, ["outputs", "gate_result"]) ||
        completion_success_result(definition)

    gate_result =
      if check["complete"] and gate_result == "UNKNOWN" do
        completion_success_result(definition)
      else
        gate_result
      end

    report = get_in(output, ["outputs", "report"]) || completion_report(check)

    output
    |> put_in(["outputs", "gate_result"], gate_result)
    |> put_in(["outputs", "report"], report)
    |> Map.put("errors", result_errors(gate_result, definition.valid_results))
    |> update_in(["metadata"], &Map.put(&1, "completion_check", check))
  end

  defp completion_success_result(definition) do
    cond do
      "PASS" in definition.valid_results -> "PASS"
      definition.valid_results != [] -> hd(definition.valid_results)
      true -> "UNKNOWN"
    end
  end

  defp completion_report(check) do
    check
    |> Map.get("diagnostics", [])
    |> Enum.map_join("\n", fn diagnostic ->
      Map.get(diagnostic, "message", inspect(diagnostic))
    end)
  end

  defp supervisor_decision_value(context) do
    context
    |> Map.get("supervisor_decision", Map.get(context, "decision", "CONTINUE"))
    |> to_string()
    |> String.upcase()
  end

  defp supervisor_feedback(context) do
    Map.get(context, "supervisor_feedback") || Map.get(context, "feedback")
  end

  defp apply_supervisor_stop(output, supervisor_context, definition) do
    gate_result =
      Map.get(supervisor_context, "gate_result") ||
        get_in(output, ["outputs", "gate_result"])

    output
    |> put_in(["outputs", "gate_result"], gate_result)
    |> Map.put("errors", result_errors(gate_result, definition.valid_results))
    |> update_in(["metadata"], fn metadata ->
      metadata
      |> Map.put("supervisor_decision", "STOP")
      |> maybe_put("supervisor_feedback", supervisor_feedback(supervisor_context))
    end)
  end

  defp restart_loop_context(context, feedback) do
    context
    |> Map.drop([
      "previous_gate_result",
      "previous_report",
      "previous_text",
      "previous_summary",
      "runtime_session_id"
    ])
    |> Map.put("supervisor_restart", true)
    |> maybe_put("supervisor_feedback", feedback)
  end

  defp truthy?(value), do: value in [true, "true", 1, "1", "yes"]

  defp max_iterations(resolved, context) do
    value =
      resolved.max_iterations ||
        get_in(context, ["policy", "max_iterations"]) ||
        1

    case value do
      integer when is_integer(integer) and integer > 0 -> integer
      binary when is_binary(binary) -> binary_max_iterations(binary)
      _other -> 1
    end
  end

  defp binary_max_iterations(value) do
    case Integer.parse(value) do
      {integer, ""} when integer > 0 -> integer
      _other -> 1
    end
  end

  defp iteration_context(context, 0), do: Map.put(context, "iteration", 0)

  defp iteration_context(context, iteration) do
    Map.merge(context, %{
      "iteration" => iteration,
      "previous_iteration" => iteration - 1
    })
  end

  defp next_loop_context(context, output) do
    runtime_session_id = get_in(output, ["metadata", "runtime_session_id"])

    context
    |> maybe_put("runtime_session_id", runtime_session_id)
    |> Map.put("previous_gate_result", get_in(output, ["outputs", "gate_result"]))
    |> Map.put("previous_report", get_in(output, ["outputs", "report"]))
    |> Map.put("previous_text", get_in(output, ["outputs", "text"]))
    |> Map.put("previous_summary", compact_summary(output))
  end

  defp terminal_gate_result?(gate_result, definition) do
    gate_result != "UNKNOWN" and gate_result in definition.valid_results
  end

  defp loop_output(output, iterations_completed, max_iterations, artifacts) do
    output
    |> Map.put("artifacts", artifacts)
    |> update_in(["metadata"], fn metadata ->
      metadata
      |> Map.put("iterations_completed", iterations_completed)
      |> Map.put("max_iterations", max_iterations)
    end)
  end

  defp add_loop_error(output, reason, details) do
    error = Map.put(details, "reason", reason)

    output
    |> update_in(["errors"], &(&1 ++ [error]))
    |> update_in(["metadata"], &Map.put(&1, "loop_status", reason))
  end

  defp turn_metadata(invocation, runtime_result) do
    %{
      "runtime" => invocation.runtime,
      "runtime_session_id" => runtime_result.session.runtime_session_id,
      "events_count" => length(runtime_result.events)
    }
  end

  defp maybe_put_iteration(metadata, nil), do: metadata
  defp maybe_put_iteration(metadata, iteration), do: Map.put(metadata, "iteration", iteration)

  defp maybe_append_continuation(objective, continuation) when continuation in [nil, ""],
    do: objective

  defp maybe_append_continuation(objective, continuation) do
    Map.update(objective, "user", continuation, fn
      nil -> continuation
      "" -> continuation
      user -> user <> "\n\n" <> continuation
    end)
  end

  defp compact_summary(output) do
    get_in(output, ["outputs", "report"]) ||
      output
      |> get_in(["outputs", "text"])
      |> compact_text()
  end

  defp compact_text(nil), do: nil

  defp compact_text(text) when is_binary(text) do
    if String.length(text) > 4_000 do
      String.slice(text, 0, 4_000)
    else
      text
    end
  end

  defp maybe_put(map, _key, nil), do: map
  defp maybe_put(map, key, value), do: Map.put(map, key, value)

  defp append_agent_event(project_root, type, agent_run_id, payload) do
    event =
      Event.new("agent_runs", type, agent_run_id, payload,
        actor: %{"type" => "agent-runner", "id" => "indexer"},
        correlation_id: Map.get(payload, "pipeline_run_id")
      )

    Jsonl.append_event!(project_root, event)
  end

  defp snapshot_config(resolved) do
    Map.take(resolved.config, [
      "max_iterations",
      "max_turns",
      "timeout_seconds",
      "runtime",
      "result_mappings"
    ])
  end

  defp duration_seconds(started_at, completed_at) do
    with {:ok, started, _} <- DateTime.from_iso8601(started_at),
         {:ok, completed, _} <- DateTime.from_iso8601(completed_at) do
      DateTime.diff(completed, started, :second)
    else
      _ -> nil
    end
  end

  defp timestamp do
    DateTime.utc_now()
    |> DateTime.truncate(:microsecond)
    |> DateTime.to_iso8601()
  end

  defp new_agent_run_id, do: "agent_run_#{System.unique_integer([:positive, :monotonic])}"
end
