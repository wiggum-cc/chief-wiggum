defmodule Indexer.Agents.RunnerTest do
  use ExUnit.Case, async: true

  alias Indexer.Agents.{Registry, Runner}
  alias Indexer.Pipeline.Run
  alias Indexer.Runtime.Session
  alias Indexer.State.Jsonl

  test "runs an agent through the runtime facade contract and records agent results" do
    root = tmp_dir()
    parent = self()
    registry = registry()

    runtime_runner = fn _root, invocation, _opts ->
      send(parent, {:invocation, invocation})

      {:ok,
       %{
         session: session(text: "<result>PASS</result><report>done</report>"),
         text: "<result>PASS</result><report>done</report>",
         events: []
       }}
    end

    assert {:ok, output} =
             Runner.run(
               root,
               "test.pass",
               %{
                 "pipeline_run_id" => "pipeline-1",
                 "node_run_id" => "node-1",
                 "step_id" => "step"
               },
               registry: registry,
               runtime_runner: runtime_runner
             )

    assert output["outputs"]["gate_result"] == "PASS"
    assert output["outputs"]["report"] == "done"
    assert output["metadata"]["runtime"] == "codex"

    assert_received {:invocation, invocation}
    assert invocation.agent_run_id == output["agent_run_id"]
    assert invocation.objective["system"] =~ "test.pass"

    events = root |> Jsonl.ledger_path("agent_runs") |> Jsonl.read!()
    assert Enum.any?(events, &(&1["type"] == "agent.started"))
    assert Enum.any?(events, &(&1["type"] == "agent.completed"))
  end

  test "bridges the ordered pipeline runner to configured agent execution" do
    root = tmp_dir()
    registry = registry()

    runtime_runner = fn _root, _invocation, _opts ->
      {:ok,
       %{
         session: session(text: "<result>PASS</result>"),
         text: "<result>PASS</result>",
         events: []
       }}
    end

    agent_runner = Runner.runner(root, registry: registry, runtime_runner: runtime_runner)
    pipeline = %{name: "agent-bridge", steps: [%{id: "work", agent: "test.pass"}]}

    assert {:ok, result} = Run.run(root, pipeline, agent_runner)
    assert result.status == "completed"

    assert root |> Jsonl.ledger_path("agent_runs") |> Jsonl.read!() |> length() == 2
  end

  test "records agent failure when prerequisites are missing" do
    root = tmp_dir()

    registry =
      Registry.from_map(%{
        agents: %{
          "test.missing": %{
            description: "Missing prerequisite",
            required_paths: ["does-not-exist"],
            valid_results: ["PASS", "FAIL"],
            mode: "once"
          }
        }
      })

    runtime_runner = fn _root, _invocation, _opts -> flunk("runtime should not be invoked") end

    assert {:error, {:missing_required_paths, [_path]}} =
             Runner.run(root, "test.missing", %{},
               registry: registry,
               runtime_runner: runtime_runner
             )

    events = root |> Jsonl.ledger_path("agent_runs") |> Jsonl.read!()
    assert Enum.any?(events, &(&1["type"] == "agent.started"))
    assert Enum.any?(events, &(&1["type"] == "agent.failed"))
  end

  test "runs plan_effects hooks and includes requested effects in output" do
    root = tmp_dir()
    registry = effects_registry()

    runtime_runner = fn _root, _invocation, _opts ->
      text = "<result>PASS</result><report>done</report>"
      {:ok, %{session: session(text: text), text: text, events: []}}
    end

    hook_runner = fn "planner", envelope ->
      assert envelope["hook"] == "plan_effects"

      {:ok,
       %{
         "effects" => [
           %{
             "effect_type" => "work_item.create",
             "scope_type" => "work_item",
             "scope_id" => "TASK-001"
           }
         ]
       }}
    end

    assert {:ok, output} =
             Runner.run(root, "test.effects", %{},
               registry: registry,
               runtime_runner: runtime_runner,
               hook_runner: hook_runner
             )

    assert [
             %{
               "effect_type" => "work_item.create",
               "scope_type" => "work_item",
               "scope_id" => "TASK-001"
             }
           ] = output["effects"]

    events = root |> Jsonl.ledger_path("agent_runs") |> Jsonl.read!()
    assert Enum.any?(events, &(&1["type"] == "agent.hook.completed"))
  end

  test "ralph_loop repeats until a terminal gate result and carries prior summary" do
    root = tmp_dir()
    parent = self()
    registry = loop_registry(max_iterations: 3)

    runtime_runner = fn _root, invocation, _opts ->
      send(parent, {:invocation, invocation.context["iteration"], invocation})

      text =
        case invocation.context["iteration"] do
          0 -> "<result>UNKNOWN</result><report>need more</report>"
          1 -> "<result>PASS</result><report>done</report>"
        end

      {:ok, %{session: session(text: text), text: text, events: []}}
    end

    assert {:ok, output} =
             Runner.run(root, "test.loop", %{},
               registry: registry,
               runtime_runner: runtime_runner
             )

    assert output["outputs"]["gate_result"] == "PASS"
    assert output["metadata"]["iterations_completed"] == 2
    assert output["metadata"]["max_iterations"] == 3
    assert output["errors"] == []

    assert_received {:invocation, 0, first}
    assert_received {:invocation, 1, second}
    refute_received {:invocation, 2, _third}

    assert first.context["iteration"] == 0
    assert second.context["iteration"] == 1
    assert second.context["previous_iteration"] == 0
    assert second.context["previous_gate_result"] == "UNKNOWN"
    assert second.context["previous_summary"] == "need more"

    events = root |> Jsonl.ledger_path("agent_runs") |> Jsonl.read!()
    assert events |> Enum.filter(&(&1["type"] == "agent.iteration.completed")) |> length() == 2
    refute Enum.any?(events, &(&1["type"] == "agent.loop.max_iterations_exceeded"))
  end

  test "ralph_loop returns UNKNOWN with a loop error when max_iterations is exhausted" do
    root = tmp_dir()
    parent = self()
    registry = loop_registry(max_iterations: 2)

    runtime_runner = fn _root, invocation, _opts ->
      send(parent, {:invocation, invocation.context["iteration"]})
      text = "<result>UNKNOWN</result><report>not done</report>"
      {:ok, %{session: session(text: text), text: text, events: []}}
    end

    assert {:ok, output} =
             Runner.run(root, "test.loop", %{},
               registry: registry,
               runtime_runner: runtime_runner
             )

    assert output["outputs"]["gate_result"] == "UNKNOWN"
    assert output["metadata"]["iterations_completed"] == 2
    assert output["metadata"]["loop_status"] == "max_iterations_exceeded"

    assert Enum.any?(output["errors"], &(&1["reason"] == "invalid_gate_result"))
    assert Enum.any?(output["errors"], &(&1["reason"] == "max_iterations_exceeded"))

    assert_received {:invocation, 0}
    assert_received {:invocation, 1}
    refute_received {:invocation, 2}

    events = root |> Jsonl.ledger_path("agent_runs") |> Jsonl.read!()
    assert Enum.any?(events, &(&1["type"] == "agent.loop.max_iterations_exceeded"))
  end

  test "ralph_loop stops when file_exists completion check passes after a turn" do
    root = tmp_dir()
    parent = self()
    output_path = Path.join(root, "done.txt")
    registry = completion_loop_registry("file_exists:{{output_path}}")

    runtime_runner = fn _root, invocation, _opts ->
      send(parent, {:invocation, invocation.context["iteration"]})
      File.write!(output_path, "done")
      text = "<result>UNKNOWN</result><report>wrote output</report>"
      {:ok, %{session: session(text: text), text: text, events: []}}
    end

    assert {:ok, output} =
             Runner.run(root, "test.completion-loop", %{"output_path" => output_path},
               registry: registry,
               runtime_runner: runtime_runner
             )

    assert output["outputs"]["gate_result"] == "PASS"
    assert output["outputs"]["report"] == "wrote output"
    assert output["metadata"]["iterations_completed"] == 1
    assert output["metadata"]["completion_check"]["type"] == "file_exists"
    assert output["errors"] == []

    assert_received {:invocation, 0}
    refute_received {:invocation, 1}

    events = root |> Jsonl.ledger_path("agent_runs") |> Jsonl.read!()
    assert Enum.any?(events, &(&1["type"] == "agent.completion_check.completed"))
  end

  test "ralph_loop can complete from a status_file before invoking the runtime" do
    root = tmp_dir()
    status_file = Path.join(root, "status.md")
    File.write!(status_file, "- [x] Done\n")

    registry = completion_loop_registry("status_file:status.md")
    runtime_runner = fn _root, _invocation, _opts -> flunk("runtime should not be invoked") end

    assert {:ok, output} =
             Runner.run(root, "test.completion-loop", %{},
               registry: registry,
               runtime_runner: runtime_runner
             )

    assert output["outputs"]["gate_result"] == "PASS"
    assert output["metadata"]["iterations_completed"] == 0
    assert output["metadata"]["completion_check"]["type"] == "status_file"
    assert output["errors"] == []
  end

  test "ralph_loop can complete from a hook completion check" do
    root = tmp_dir()
    registry = hook_completion_loop_registry()

    hook_runner = fn "done-check", envelope ->
      assert envelope["hook"] == "done"
      {:ok, %{"complete" => true, "gate_result" => "PASS"}}
    end

    runtime_runner = fn _root, _invocation, _opts -> flunk("runtime should not be invoked") end

    assert {:ok, output} =
             Runner.run(root, "test.hook-completion-loop", %{},
               registry: registry,
               hook_runner: hook_runner,
               runtime_runner: runtime_runner
             )

    assert output["outputs"]["gate_result"] == "PASS"
    assert output["metadata"]["completion_check"]["type"] == "hook"
    assert output["metadata"]["iterations_completed"] == 0
  end

  test "ralph_loop supervisor hook can continue with feedback" do
    root = tmp_dir()
    parent = self()
    registry = supervisor_loop_registry()

    runtime_runner = fn _root, invocation, _opts ->
      send(parent, {:invocation, invocation.context["iteration"], invocation.context})

      text =
        if invocation.context["supervisor_feedback"] == "tighten" do
          "<result>PASS</result><report>done</report>"
        else
          "<result>UNKNOWN</result><report>needs review</report>"
        end

      {:ok, %{session: session(text: text), text: text, events: []}}
    end

    hook_runner = fn "supervisor-hook", envelope ->
      assert envelope["hook"] == "supervisor"
      {:ok, %{"supervisor_decision" => "CONTINUE", "supervisor_feedback" => "tighten"}}
    end

    assert {:ok, output} =
             Runner.run(root, "test.supervised-loop", %{},
               registry: registry,
               runtime_runner: runtime_runner,
               hook_runner: hook_runner
             )

    assert output["outputs"]["gate_result"] == "PASS"
    assert output["metadata"]["iterations_completed"] == 2

    assert_received {:invocation, 0, first_context}
    assert_received {:invocation, 1, second_context}
    assert first_context["supervisor_feedback"] == nil
    assert second_context["supervisor_feedback"] == "tighten"

    events = root |> Jsonl.ledger_path("agent_runs") |> Jsonl.read!()
    assert Enum.any?(events, &(&1["type"] == "agent.supervisor.completed"))
  end

  test "ralph_loop supervisor hook can stop with a gate result" do
    root = tmp_dir()
    parent = self()
    registry = supervisor_loop_registry()

    runtime_runner = fn _root, invocation, _opts ->
      send(parent, {:invocation, invocation.context["iteration"]})
      text = "<result>UNKNOWN</result><report>blocked</report>"
      {:ok, %{session: session(text: text), text: text, events: []}}
    end

    hook_runner = fn "supervisor-hook", _envelope ->
      {:ok,
       %{
         "supervisor_decision" => "STOP",
         "supervisor_feedback" => "not recoverable",
         "gate_result" => "FAIL"
       }}
    end

    assert {:ok, output} =
             Runner.run(root, "test.supervised-loop", %{},
               registry: registry,
               runtime_runner: runtime_runner,
               hook_runner: hook_runner
             )

    assert output["outputs"]["gate_result"] == "FAIL"
    assert output["metadata"]["iterations_completed"] == 1
    assert output["metadata"]["supervisor_decision"] == "STOP"
    assert output["metadata"]["supervisor_feedback"] == "not recoverable"

    assert_received {:invocation, 0}
    refute_received {:invocation, 1}
  end

  test "ralph_loop appends markdown continuation only after the first iteration" do
    root = tmp_dir()
    parent = self()
    registry = markdown_loop_registry(root)

    runtime_runner = fn _root, invocation, _opts ->
      send(parent, {:objective, invocation.context["iteration"], invocation.objective})

      text =
        case invocation.context["iteration"] do
          0 -> "<result>UNKNOWN</result><report>draft summary</report>"
          1 -> "<result>PASS</result><report>done</report>"
        end

      {:ok, %{session: session(text: text), text: text, events: []}}
    end

    assert {:ok, output} =
             Runner.run(root, "test.markdown-loop", %{},
               registry: registry,
               runtime_runner: runtime_runner
             )

    assert output["outputs"]["gate_result"] == "PASS"

    assert_received {:objective, 0, first}
    assert_received {:objective, 1, second}

    assert first["continuation"] == nil
    refute first["user"] =~ "Continue after"

    assert second["continuation"] =~ "Continue after 0"
    assert second["continuation"] =~ "draft summary"
    assert second["user"] =~ "Continue after 0"
    assert second["user"] =~ "draft summary"
  end

  defp registry do
    Registry.from_map(%{
      defaults: %{
        description: "Configured test agent",
        required_paths: ["workspace"],
        valid_results: ["PASS", "FAIL"],
        mode: "once",
        runtime: %{adapter: "codex", mode: "cli_text"},
        result_mappings: %{
          PASS: %{status: "success", exit_code: 0, default_jump: "next"},
          FAIL: %{status: "failure", exit_code: 10, default_jump: "abort"}
        }
      },
      agents: %{
        "test.pass": %{}
      }
    })
  end

  defp effects_registry do
    Registry.from_map(%{
      defaults: %{
        description: "Effect planning agent",
        required_paths: ["workspace"],
        valid_results: ["PASS", "FAIL"],
        mode: "once",
        runtime: %{adapter: "codex", mode: "cli_text"}
      },
      agents: %{
        "test.effects": %{
          hooks: %{"plan_effects" => ["planner"]}
        }
      }
    })
  end

  defp loop_registry(opts) do
    max_iterations = Keyword.fetch!(opts, :max_iterations)

    Registry.from_map(%{
      defaults: %{
        description: "Configured loop agent",
        required_paths: ["workspace"],
        valid_results: ["PASS", "FAIL"],
        mode: "once",
        runtime: %{adapter: "codex", mode: "cli_text"},
        result_mappings: %{
          PASS: %{status: "success", exit_code: 0, default_jump: "next"},
          FAIL: %{status: "failure", exit_code: 10, default_jump: "abort"}
        }
      },
      agents: %{
        "test.loop": %{
          mode: "ralph_loop",
          max_iterations: max_iterations
        }
      }
    })
  end

  defp hook_completion_loop_registry do
    Registry.from_map(%{
      defaults: %{
        description: "Hook completion loop agent",
        required_paths: ["workspace"],
        valid_results: ["PASS", "FAIL"],
        mode: "once",
        runtime: %{adapter: "codex", mode: "cli_text"}
      },
      agents: %{
        "test.hook-completion-loop": %{
          mode: "ralph_loop",
          max_iterations: 3,
          completion_check: "hook:done",
          hooks: %{"done" => ["done-check"]}
        }
      }
    })
  end

  defp supervisor_loop_registry do
    Registry.from_map(%{
      defaults: %{
        description: "Supervised loop agent",
        required_paths: ["workspace"],
        valid_results: ["PASS", "FAIL"],
        mode: "once",
        runtime: %{adapter: "codex", mode: "cli_text"}
      },
      agents: %{
        "test.supervised-loop": %{
          mode: "ralph_loop",
          max_iterations: 3,
          supervisor_interval: 1,
          hooks: %{"supervisor" => ["supervisor-hook"]}
        }
      }
    })
  end

  defp completion_loop_registry(completion_check) do
    Registry.from_map(%{
      defaults: %{
        description: "Completion loop agent",
        required_paths: ["workspace"],
        valid_results: ["PASS", "FAIL"],
        mode: "once",
        runtime: %{adapter: "codex", mode: "cli_text"},
        result_mappings: %{
          PASS: %{status: "success", exit_code: 0, default_jump: "next"},
          FAIL: %{status: "failure", exit_code: 10, default_jump: "abort"}
        }
      },
      agents: %{
        "test.completion-loop": %{
          mode: "ralph_loop",
          max_iterations: 3,
          completion_check: completion_check
        }
      }
    })
  end

  defp markdown_loop_registry(root) do
    agents_dir = Path.join(root, "agents")
    File.mkdir_p!(agents_dir)

    File.write!(Path.join(agents_dir, "loop.md"), """
    ---
    type: test.markdown-loop
    description: Markdown loop agent
    required_paths: [workspace]
    valid_results: [PASS, FAIL]
    mode: ralph_loop
    ---

    <INDEXER_SYSTEM_PROMPT>
    System iteration {{iteration}}.
    </INDEXER_SYSTEM_PROMPT>

    <INDEXER_USER_PROMPT>
    Work iteration {{iteration}}.
    <INDEXER_IF_CONTEXT:previous_summary>
    Previous summary: {{previous_summary}}.
    </INDEXER_IF_CONTEXT>
    </INDEXER_USER_PROMPT>

    <INDEXER_CONTINUATION_PROMPT>
    Continue after {{previous_iteration}} with {{previous_summary}}.
    </INDEXER_CONTINUATION_PROMPT>
    """)

    Registry.from_map(
      %{
        defaults: %{
          runtime: %{adapter: "codex", mode: "cli_text"},
          max_iterations: 2,
          result_mappings: %{
            PASS: %{status: "success", exit_code: 0, default_jump: "next"},
            FAIL: %{status: "failure", exit_code: 10, default_jump: "abort"}
          }
        },
        agents: %{
          "test.markdown-loop": %{
            definition: "agents/loop.md"
          }
        }
      },
      root
    )
  end

  defp session(attrs) when is_list(attrs), do: session(Map.new(attrs))

  defp session(attrs) do
    defaults = %{
      runtime: "codex",
      mode: "cli_text",
      status: "completed",
      started_at: DateTime.utc_now() |> DateTime.truncate(:microsecond) |> DateTime.to_iso8601()
    }

    struct!(Session, Map.merge(defaults, attrs))
  end

  defp tmp_dir do
    path =
      Path.join(System.tmp_dir!(), "indexer-runner-test-#{System.unique_integer([:positive])}")

    File.rm_rf!(path)
    File.mkdir_p!(path)
    path
  end
end
