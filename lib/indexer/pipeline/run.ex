defmodule Indexer.Pipeline.Run do
  @moduledoc """
  Ordered-step pipeline executor.

  This module implements the first Elixir version of the v1 jump-based state
  machine. It accepts an injected agent runner so runtime adapters can be wired
  separately.
  """

  alias Indexer.Effects.{Effect, Outbox}
  alias Indexer.Pipeline.{ResultMappings, Schema}
  alias Indexer.State.{Event, Jsonl}

  @terminal_results MapSet.new(["PASS", "FAIL", "SKIP"])
  @default_max_transitions 1_000

  @type agent_runner ::
          (String.t(), map() -> String.t() | map() | {:ok, String.t() | map()} | {:error, term()})

  @type run_result :: %{
          required(:status) => String.t(),
          required(:pipeline_run_id) => String.t(),
          required(:history) => [map()]
        }

  @doc """
  Runs a validated pipeline map.
  """
  @spec run(Path.t(), map(), agent_runner(), keyword()) :: {:ok, run_result()} | {:error, term()}
  def run(project_root, pipeline, agent_runner, opts \\ [])
      when is_binary(project_root) and is_map(pipeline) and is_function(agent_runner, 2) do
    pipeline = Indexer.State.Json.normalize(pipeline)

    with :ok <- Schema.validate(pipeline) do
      state = initial_state(project_root, pipeline, agent_runner, opts)

      append_pipeline_event(state, "pipeline.started", %{
        pipeline: Map.take(pipeline, ["name", "description"])
      })

      case execute(state) do
        {:ok, final_state} ->
          append_pipeline_event(final_state, "pipeline.#{final_state.status}", %{
            status: final_state.status,
            current_step_index: final_state.pc,
            history_count: length(final_state.history)
          })

          {:ok,
           %{
             status: final_state.status,
             pipeline_run_id: final_state.pipeline_run_id,
             history: Enum.reverse(final_state.history)
           }}

        {:error, reason, failed_state} ->
          append_pipeline_event(failed_state, "pipeline.failed", %{reason: inspect(reason)})
          {:error, reason}
      end
    end
  end

  defp initial_state(project_root, pipeline, agent_runner, opts) do
    steps = Map.fetch!(pipeline, "steps")

    %{
      project_root: project_root,
      pipeline: pipeline,
      steps: steps,
      id_to_index: build_id_index(steps),
      pipeline_run_id: Keyword.get_lazy(opts, :pipeline_run_id, &new_pipeline_run_id/0),
      agent_runner: agent_runner,
      hook_runner: Keyword.get(opts, :hook_runner, &Indexer.Hooks.Executor.run/2),
      context: Indexer.State.Json.normalize(Keyword.get(opts, :context, %{})),
      env: stringify_map(Keyword.get(opts, :env, %{})),
      pc: start_index(steps, Keyword.get(opts, :start_from)),
      visits: %{},
      inline_visits: %{},
      consecutive: %{},
      transitions: 0,
      max_transitions: Keyword.get(opts, :max_transitions, @default_max_transitions),
      history: [],
      status: "running",
      correlation_id: Keyword.get(opts, :correlation_id),
      actor: Keyword.get(opts, :actor, %{"type" => "service", "id" => "pipeline-engine"})
    }
  end

  defp execute(%{status: status} = state) when status in ["completed", "aborted"],
    do: {:ok, state}

  defp execute(%{transitions: transitions, max_transitions: max} = state)
       when transitions >= max do
    {:error, :max_transitions_exceeded, %{state | status: "aborted"}}
  end

  defp execute(%{pc: pc, steps: steps} = state) when pc >= length(steps) do
    {:ok, %{state | status: "completed"}}
  end

  defp execute(%{pc: pc} = state) when pc < 0 do
    {:ok, %{state | status: "aborted"}}
  end

  defp execute(state) do
    state
    |> step()
    |> case do
      {:ok, next_state} -> execute(%{next_state | transitions: next_state.transitions + 1})
      {:error, reason, next_state} -> {:error, reason, next_state}
    end
  end

  defp step(%{pc: pc, steps: steps} = state) do
    step = Enum.at(steps, pc)
    step_id = Map.fetch!(step, "id")

    cond do
      not enabled?(state, step) ->
        node_run_id = new_node_run_id()

        state
        |> append_node_event("pipeline.node.skipped", node_run_id, step, %{
          reason: "enabled_by_false",
          visit: visit_count(state, step_id)
        })
        |> add_history(%{
          "step_id" => step_id,
          "node_run_id" => node_run_id,
          "gate_result" => "SKIP",
          "effective_result" => "SKIP",
          "next_step_id" => next_step_id(state, pc + 1),
          "inline" => false
        })
        |> jump_to("next", pc)

      max_exceeded?(state, step_id, step) ->
        on_max = Map.get(step, "on_max", "next")

        state
        |> append_node_event("pipeline.node.max_exceeded", new_node_run_id(), step, %{
          visit: visit_count(state, step_id),
          on_max: on_max
        })
        |> jump_to(on_max, pc)

      true ->
        run_top_level_step(state, step)
    end
  end

  defp run_top_level_step(state, step) do
    step_id = Map.fetch!(step, "id")
    node_run_id = new_node_run_id()
    visit = visit_count(state, step_id) + 1

    state =
      state
      |> put_in([:visits, step_id], visit)
      |> append_node_event("pipeline.node.started", node_run_id, step, %{
        visit: visit,
        inline: false
      })

    readonly_snapshot = readonly_snapshot(state, step)

    state =
      state
      |> run_hooks(step, node_run_id, "pre", %{"visit" => visit, "inline" => false})

    case call_agent(state, step, node_run_id, false) do
      {:ok, output} ->
        state =
          state
          |> restore_readonly(step, node_run_id, readonly_snapshot)
          |> run_hooks(step, node_run_id, "post", %{
            "visit" => visit,
            "inline" => false,
            "output" => output
          })

        route_step_result(state, step, node_run_id, output, visit, false)

      {:error, reason} ->
        failed =
          state
          |> restore_readonly(step, node_run_id, readonly_snapshot)
          |> append_node_event("pipeline.node.failed", node_run_id, step, %{
            reason: inspect(reason)
          })

        {:error, reason, failed}
    end
  end

  defp route_step_result(state, step, node_run_id, output, visit, inline?) do
    raw_result = extract_gate_result(output)
    {state, effective_result} = apply_circuit_breaker(state, step, node_run_id, raw_result)

    case ResultMappings.resolve(
           effective_result,
           Map.get(state.pipeline, "result_mappings", %{}),
           Map.get(step, "result_mappings", %{})
         ) do
      {:ok, mapping} ->
        state =
          append_node_event(state, "pipeline.node.completed", node_run_id, step, %{
            visit: visit,
            inline: inline?,
            raw_result: raw_result,
            gate_result: effective_result,
            status: mapping["status"],
            exit_code: mapping["exit_code"],
            default_jump: mapping["default_jump"],
            outputs: output
          })
          |> maybe_request_commit_after(step, node_run_id, output, mapping)

        route_from_result(state, step, effective_result, mapping)

      {:error, :unknown_result} ->
        failed =
          append_node_event(state, "pipeline.node.failed", node_run_id, step, %{
            visit: visit,
            raw_result: raw_result,
            reason: "unknown_result"
          })

        {:error, {:unknown_result, raw_result}, failed}
    end
  end

  defp route_from_result(state, step, result, mapping) do
    handler = get_in(step, ["on_result", result])

    cond do
      is_map(handler) and Map.has_key?(handler, "jump") ->
        state
        |> add_result_history(step, result, result, handler["jump"], false)
        |> jump_to(handler["jump"], state.pc)

      is_map(handler) and Map.has_key?(handler, "agent") ->
        run_inline_handler(state, step, handler, result)

      true ->
        jump = mapping["default_jump"]

        state
        |> add_result_history(step, result, result, jump, false)
        |> jump_to(jump, state.pc)
    end
  end

  defp run_inline_handler(state, parent_step, handler, parent_result) do
    parent_idx = state.pc
    handler_id = Map.fetch!(handler, "id")

    cond do
      max_exceeded?(state, handler_id, handler, :inline_visits) ->
        state
        |> append_node_event("pipeline.inline.max_exceeded", new_node_run_id(), handler, %{
          parent_step_id: parent_step["id"],
          parent_result: parent_result,
          visit: Map.get(state.inline_visits, handler_id, 0),
          on_max: Map.get(handler, "on_max", "next")
        })
        |> jump_to(Map.get(handler, "on_max", "next"), parent_idx)

      true ->
        node_run_id = new_node_run_id()
        visit = Map.get(state.inline_visits, handler_id, 0) + 1

        state =
          state
          |> put_in([:inline_visits, handler_id], visit)
          |> append_node_event("pipeline.inline.started", node_run_id, handler, %{
            parent_step_id: parent_step["id"],
            parent_result: parent_result,
            visit: visit,
            inline: true
          })

        readonly_snapshot = readonly_snapshot(state, handler)

        state =
          state
          |> run_hooks(handler, node_run_id, "pre", %{
            "parent_step_id" => parent_step["id"],
            "parent_result" => parent_result,
            "visit" => visit,
            "inline" => true
          })

        case call_agent(state, handler, node_run_id, true) do
          {:ok, output} ->
            state =
              state
              |> restore_readonly(handler, node_run_id, readonly_snapshot)
              |> run_hooks(handler, node_run_id, "post", %{
                "parent_step_id" => parent_step["id"],
                "visit" => visit,
                "inline" => true,
                "output" => output
              })

            route_inline_result(state, parent_step, handler, node_run_id, output, visit)

          {:error, reason} ->
            failed =
              state
              |> restore_readonly(handler, node_run_id, readonly_snapshot)
              |> append_node_event("pipeline.inline.failed", node_run_id, handler, %{
                reason: inspect(reason)
              })

            {:error, reason, failed}
        end
    end
  end

  defp route_inline_result(state, parent_step, handler, node_run_id, output, visit) do
    raw_result = extract_gate_result(output)
    {state, effective_result} = apply_circuit_breaker(state, handler, node_run_id, raw_result)

    case ResultMappings.resolve(
           effective_result,
           Map.get(state.pipeline, "result_mappings", %{}),
           Map.get(handler, "result_mappings", %{})
         ) do
      {:ok, mapping} ->
        state =
          append_node_event(state, "pipeline.inline.completed", node_run_id, handler, %{
            parent_step_id: parent_step["id"],
            visit: visit,
            inline: true,
            raw_result: raw_result,
            gate_result: effective_result,
            status: mapping["status"],
            exit_code: mapping["exit_code"],
            default_jump: mapping["default_jump"],
            outputs: output
          })
          |> maybe_request_commit_after(handler, node_run_id, output, mapping)

        inline_handler = get_in(handler, ["on_result", effective_result])

        cond do
          is_map(inline_handler) and Map.has_key?(inline_handler, "jump") ->
            state
            |> add_result_history(
              handler,
              raw_result,
              effective_result,
              inline_handler["jump"],
              true
            )
            |> jump_to(inline_handler["jump"], state.pc)

          is_map(inline_handler) and Map.has_key?(inline_handler, "agent") ->
            run_inline_handler(state, parent_step, inline_handler, effective_result)

          true ->
            state
            |> add_result_history(handler, raw_result, effective_result, parent_step["id"], true)
            |> jump_to(parent_step["id"], state.pc)
        end

      {:error, :unknown_result} ->
        failed =
          append_node_event(state, "pipeline.inline.failed", node_run_id, handler, %{
            visit: visit,
            raw_result: raw_result,
            reason: "unknown_result"
          })

        {:error, {:unknown_result, raw_result}, failed}
    end
  end

  defp call_agent(state, step, node_run_id, inline?) do
    context =
      Indexer.Agents.Registry.deep_merge(state.context, %{
        "pipeline_run_id" => state.pipeline_run_id,
        "node_run_id" => node_run_id,
        "step_id" => step["id"],
        "agent" => step["agent"],
        "inline" => inline?,
        "project_root" => state.project_root,
        "config" => step_config(step)
      })

    case state.agent_runner.(step["agent"], context) do
      {:ok, result} -> {:ok, normalize_agent_output(result)}
      {:error, reason} -> {:error, reason}
      result -> {:ok, normalize_agent_output(result)}
    end
  rescue
    exception -> {:error, {exception.__struct__, Exception.message(exception)}}
  end

  defp run_hooks(state, step, node_run_id, phase, extra_context) do
    step
    |> get_in(["hooks", phase])
    |> List.wrap()
    |> Enum.reduce(state, fn hook, acc ->
      envelope = hook_envelope(acc, step, node_run_id, phase, extra_context)

      case acc.hook_runner.(hook, envelope) do
        {:ok, result} ->
          append_node_event(acc, "pipeline.hook.completed", node_run_id, step, %{
            hook_phase: phase,
            hook: hook,
            result: result
          })

        {:error, error} ->
          append_node_event(acc, "pipeline.hook.failed", node_run_id, step, %{
            hook_phase: phase,
            hook: hook,
            error: error
          })

        other ->
          append_node_event(acc, "pipeline.hook.failed", node_run_id, step, %{
            hook_phase: phase,
            hook: hook,
            error: inspect(other)
          })
      end
    end)
  end

  defp hook_envelope(state, step, node_run_id, phase, extra_context) do
    %{
      "hook" => phase,
      "agent_id" => step["agent"],
      "pipeline_run" => %{
        "id" => state.pipeline_run_id,
        "name" => state.pipeline["name"]
      },
      "node_run" => %{
        "id" => node_run_id,
        "step_id" => step["id"]
      },
      "workspace" => %{},
      "repository" => %{"project_root" => state.project_root},
      "context" => extra_context,
      "artifacts" => [],
      "config" => Map.get(step, "config", %{})
    }
  end

  defp normalize_agent_output(result) when is_binary(result),
    do: %{"outputs" => %{"gate_result" => result}}

  defp normalize_agent_output(%{} = result), do: Indexer.State.Json.normalize(result)

  defp normalize_agent_output(other), do: %{"outputs" => %{"gate_result" => to_string(other)}}

  defp step_config(step) do
    step
    |> Map.get("config", %{})
    |> maybe_put_step_config(step, "timeout_seconds")
    |> maybe_put_step_config(step, "max_iterations")
    |> maybe_put_step_config(step, "max_turns")
    |> maybe_put_step_config(step, "readonly")
  end

  defp maybe_put_step_config(config, step, key) do
    case Map.fetch(step, key) do
      {:ok, value} -> Map.put(config, key, value)
      :error -> config
    end
  end

  defp maybe_request_commit_after(state, step, node_run_id, output, mapping) do
    if Map.get(step, "commit_after", false) and not Map.get(step, "readonly", false) and
         mapping["status"] == "success" do
      effect =
        Effect.new(
          "git.commit_workspace",
          "node_run",
          node_run_id,
          commit_effect_payload(state, step, node_run_id, output),
          idempotency_key: "git.commit_workspace:#{node_run_id}:#{output_fingerprint(output)}"
        )

      Outbox.record_pending!(state.project_root, effect,
        actor: state.actor,
        causation_id: node_run_id,
        correlation_id: state.pipeline_run_id
      )

      append_node_event(state, "pipeline.node.effect_requested", node_run_id, step, %{
        effect_id: effect.id,
        effect_type: effect.effect_type,
        idempotency_key: effect.idempotency_key
      })
    else
      state
    end
  end

  defp readonly_snapshot(state, %{"readonly" => true}) do
    workspace = Map.get(state.context, "workspace") || state.project_root

    cond do
      not Indexer.Git.Repository.repo?(workspace) ->
        %{
          "enabled" => true,
          "workspace" => workspace,
          "restorable" => false,
          "reason" => "not_git_repository"
        }

      not Indexer.Git.Repository.clean?(workspace) ->
        %{
          "enabled" => true,
          "workspace" => workspace,
          "restorable" => false,
          "reason" => "dirty_before"
        }

      true ->
        %{"enabled" => true, "workspace" => workspace, "restorable" => true}
    end
  end

  defp readonly_snapshot(_state, _step), do: %{"enabled" => false}

  defp restore_readonly(state, _step, _node_run_id, %{"enabled" => false}), do: state

  defp restore_readonly(state, step, node_run_id, %{
         "restorable" => true,
         "workspace" => workspace
       }) do
    case Indexer.Git.Repository.git(workspace, ["restore", "--staged", "--worktree", "."]) do
      {:ok, _} ->
        append_node_event(state, "pipeline.node.readonly_restored", node_run_id, step, %{
          workspace: workspace
        })

      {:error, error} ->
        append_node_event(state, "pipeline.node.readonly_restore_failed", node_run_id, step, %{
          workspace: workspace,
          error: error
        })
    end
  end

  defp restore_readonly(state, step, node_run_id, snapshot) do
    append_node_event(state, "pipeline.node.readonly_restore_skipped", node_run_id, step, %{
      workspace: snapshot["workspace"],
      reason: snapshot["reason"]
    })
  end

  defp commit_effect_payload(state, step, node_run_id, output) do
    %{
      "workspace_path" => Map.get(state.context, "workspace") || state.project_root,
      "pipeline_run_id" => state.pipeline_run_id,
      "node_run_id" => node_run_id,
      "step_id" => step["id"],
      "agent" => step["agent"],
      "message" => commit_message(state, step, output)
    }
  end

  defp commit_message(state, step, output) do
    summary =
      get_in(output, ["outputs", "report"]) ||
        get_in(output, ["outputs", "text"]) ||
        "Pipeline step completed."

    "Indexer: #{state.pipeline["name"]}/#{step["id"]} (#{step["agent"]})\n\n" <>
      String.slice(summary, 0, 1_000)
  end

  defp output_fingerprint(output) do
    :sha256
    |> :crypto.hash(JSON.encode!(output))
    |> Base.encode16(case: :lower)
    |> String.slice(0, 16)
  end

  defp extract_gate_result(%{"outputs" => %{"gate_result" => result}}) when is_binary(result),
    do: result

  defp extract_gate_result(%{"gate_result" => result}) when is_binary(result), do: result
  defp extract_gate_result(_output), do: "UNKNOWN"

  defp apply_circuit_breaker(%{consecutive: consecutive} = state, step, node_run_id, result) do
    step_id = Map.fetch!(step, "id")
    previous = Map.get(consecutive, step_id, %{"result" => nil, "count" => 0})

    count =
      cond do
        MapSet.member?(@terminal_results, result) -> 0
        previous["result"] == result -> previous["count"] + 1
        true -> 1
      end

    state = put_in(state.consecutive[step_id], %{"result" => result, "count" => count})

    threshold = 3

    if count >= threshold and not MapSet.member?(@terminal_results, result) do
      state =
        append_node_event(state, "pipeline.node.circuit_tripped", node_run_id, step, %{
          repeated_result: result,
          count: count,
          threshold: threshold,
          effective_result: "FAIL"
        })

      {state, "FAIL"}
    else
      {state, result}
    end
  end

  defp enabled?(_state, %{"enabled_by" => nil}), do: true
  defp enabled?(_state, step) when not is_map_key(step, "enabled_by"), do: true

  defp enabled?(state, %{"enabled_by" => key}) when is_binary(key) do
    state.env
    |> Map.get(key, System.get_env(key))
    |> truthy?()
  end

  defp enabled?(_state, _step), do: true

  defp truthy?(value) when value in [true, "true", "1", "yes", "on"], do: true
  defp truthy?(_value), do: false

  defp max_exceeded?(state, step_id, step, counter_key \\ :visits) do
    max = Map.get(step, "max", 0)
    max > 0 and Map.get(Map.fetch!(state, counter_key), step_id, 0) >= max
  end

  defp visit_count(state, step_id), do: Map.get(state.visits, step_id, 0)

  defp jump_to(state, target, current_idx) do
    next_pc = resolve_jump(state, target, current_idx)
    {:ok, %{state | pc: next_pc}}
  end

  defp resolve_jump(_state, "self", current_idx), do: current_idx
  defp resolve_jump(_state, "prev", current_idx), do: max(current_idx - 1, 0)
  defp resolve_jump(_state, "next", current_idx), do: current_idx + 1
  defp resolve_jump(_state, "abort", _current_idx), do: -1
  defp resolve_jump(state, step_id, _current_idx), do: Map.fetch!(state.id_to_index, step_id)

  defp append_pipeline_event(state, type, payload) do
    event =
      Event.new("pipeline_runs", type, state.pipeline_run_id, payload,
        actor: state.actor,
        correlation_id: state.correlation_id
      )

    Jsonl.append_event!(state.project_root, event)
    state
  end

  defp append_node_event(state, type, node_run_id, step, payload) do
    payload =
      Map.merge(
        %{
          "pipeline_run_id" => state.pipeline_run_id,
          "node_run_id" => node_run_id,
          "step_id" => step["id"],
          "agent" => step["agent"]
        },
        Indexer.State.Json.normalize(payload)
      )

    event =
      Event.new("pipeline_node_runs", type, node_run_id, payload,
        actor: state.actor,
        correlation_id: state.pipeline_run_id
      )

    Jsonl.append_event!(state.project_root, event)
    state
  end

  defp add_result_history(state, step, raw_result, effective_result, jump, inline?) do
    add_history(state, %{
      "step_id" => step["id"],
      "agent" => step["agent"],
      "gate_result" => raw_result,
      "effective_result" => effective_result,
      "jump" => jump,
      "inline" => inline?
    })
  end

  defp add_history(state, entry), do: %{state | history: [entry | state.history]}

  defp build_id_index(steps) do
    steps
    |> Enum.with_index()
    |> Map.new(fn {step, index} -> {step["id"], index} end)
  end

  defp start_index(_steps, nil), do: 0

  defp start_index(steps, step_id) when is_binary(step_id),
    do: steps |> build_id_index() |> Map.fetch!(step_id)

  defp next_step_id(_state, pc) when pc < 0, do: nil
  defp next_step_id(%{steps: steps}, pc) when pc >= length(steps), do: nil
  defp next_step_id(%{steps: steps}, pc), do: Enum.at(steps, pc)["id"]

  defp stringify_map(map) do
    Map.new(map, fn {key, value} -> {to_string(key), value} end)
  end

  defp new_pipeline_run_id, do: "pipeline_run_#{System.unique_integer([:positive, :monotonic])}"
  defp new_node_run_id, do: "node_run_#{System.unique_integer([:positive, :monotonic])}"
end
