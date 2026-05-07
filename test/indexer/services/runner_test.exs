defmodule Indexer.Services.RunnerTest do
  use ExUnit.Case, async: true

  alias Indexer.Services.{Runner, State}
  alias Indexer.State.Jsonl

  test "runs an allowlisted function service and records lifecycle events" do
    root = tmp_dir()

    service = %{
      id: "validate-control",
      phase: "startup",
      schedule: %{type: "tick"},
      execution: %{
        type: "function",
        module: "Indexer.Services.Handlers.Control",
        function: "validate"
      }
    }

    assert {:ok, result} = Runner.run(root, service)
    assert result["status"] == "success"

    events = root |> Jsonl.ledger_path("services") |> Jsonl.read!()
    assert Enum.map(events, & &1["type"]) == ["service.started", "service.completed"]
    assert State.get(root, "validate-control")["run_count"] == 1
  end

  test "runs argv command services without shell evaluation by default" do
    root = tmp_dir()

    service = %{
      id: "command",
      schedule: %{type: "tick"},
      execution: %{type: "command", command: ["printf", "ok"]}
    }

    assert {:ok, result} = Runner.run(root, service)
    assert result["output"]["stdout"] == "ok"
  end

  test "skips a running singleton service according to concurrency policy" do
    root = tmp_dir()

    service = %{
      id: "singleton",
      schedule: %{type: "tick"},
      execution: %{type: "command", command: ["printf", "ok"]},
      concurrency: %{max_instances: 1, if_running: "skip"}
    }

    append_started(root, "singleton")

    assert {:ok, result} = Runner.run(root, service)
    assert result["status"] == "skipped"
    assert result["reason"] == "already_running"
  end

  test "retries failed services according to restart policy" do
    root = tmp_dir()
    parent = self()

    service = %{
      id: "retrying",
      schedule: %{type: "tick"},
      execution: %{type: "function"},
      restart_policy: %{
        on_failure: "retry",
        max_retries: 1,
        backoff: %{initial: 0, multiplier: 2, max: 10}
      }
    }

    function_runner = fn _execution, _service, _context, _opts ->
      attempt = Process.get(:service_attempt, 0)
      Process.put(:service_attempt, attempt + 1)
      send(parent, {:attempt, attempt})

      if attempt == 0 do
        {:error, %{exit_code: 2, errors: [%{"reason" => "transient"}]}}
      else
        {:ok, %{"ok" => true}}
      end
    end

    sleep_fun = fn milliseconds -> send(parent, {:sleep, milliseconds}) end

    assert {:ok, result} =
             Runner.run(root, service, function_runner: function_runner, sleep_fun: sleep_fun)

    assert result["status"] == "success"
    assert result["attempt"] == 1
    assert_received {:attempt, 0}
    assert_received {:sleep, 0}
    assert_received {:attempt, 1}

    events = root |> Jsonl.ledger_path("services") |> Jsonl.read!()

    assert Enum.map(events, & &1["type"]) == [
             "service.started",
             "service.completed",
             "service.retry_scheduled",
             "service.started",
             "service.completed"
           ]

    state = State.get(root, "retrying")
    assert state["run_count"] == 1
    assert state["fail_count"] == 1
    assert state["consecutive_failures"] == 0
  end

  test "does not retry when restart policy skips failures" do
    root = tmp_dir()

    service = %{
      id: "no-retry",
      schedule: %{type: "tick"},
      execution: %{type: "function"},
      restart_policy: %{on_failure: "skip", max_retries: 5}
    }

    function_runner = fn _execution, _service, _context, _opts ->
      {:error, %{exit_code: 2, errors: [%{"reason" => "permanent"}]}}
    end

    assert {:error, result} = Runner.run(root, service, function_runner: function_runner)
    assert result["status"] == "failure"
    assert result["attempt"] == 0

    events = root |> Jsonl.ledger_path("services") |> Jsonl.read!()
    assert Enum.map(events, & &1["type"]) == ["service.started", "service.completed"]
  end

  test "opens circuit after threshold failures and skips later runs" do
    root = tmp_dir()
    parent = self()

    service = %{
      id: "circuit",
      schedule: %{type: "tick"},
      execution: %{type: "function"},
      circuit_breaker: %{enabled: true, threshold: 1, cooldown: 300}
    }

    failing_runner = fn _execution, _service, _context, _opts ->
      send(parent, :attempted)
      {:error, %{exit_code: 2, errors: [%{"reason" => "failed"}]}}
    end

    assert {:error, _result} = Runner.run(root, service, function_runner: failing_runner)
    assert State.get(root, "circuit")["circuit_state"] == "open"

    assert {:ok, skipped} = Runner.run(root, service, function_runner: failing_runner)
    assert skipped["status"] == "skipped"
    assert skipped["reason"] == "circuit_open"

    assert_received :attempted
    refute_received :attempted
  end

  test "allows a half-open circuit trial after cooldown" do
    root = tmp_dir()

    service = %{
      id: "half-open",
      schedule: %{type: "tick"},
      execution: %{type: "function"},
      circuit_breaker: %{enabled: true, threshold: 1, cooldown: 1}
    }

    append_circuit_opened(root, "half-open", DateTime.add(DateTime.utc_now(), -5, :second))

    function_runner = fn _execution, _service, _context, _opts ->
      {:ok, %{"trial" => "passed"}}
    end

    assert {:ok, result} = Runner.run(root, service, function_runner: function_runner)
    assert result["status"] == "success"

    events = root |> Jsonl.ledger_path("services") |> Jsonl.read!()
    assert Enum.any?(events, &(&1["type"] == "service.circuit_half_opened"))
    assert Enum.any?(events, &(&1["type"] == "service.circuit_closed"))
    assert State.get(root, "half-open")["circuit_state"] == "closed"
  end

  defp append_started(root, service_id) do
    event =
      Indexer.State.Event.new("services", "service.started", "service:#{service_id}", %{
        service_id: service_id,
        run_id: "run-1",
        started_at: DateTime.utc_now() |> DateTime.truncate(:microsecond) |> DateTime.to_iso8601()
      })

    Jsonl.append_event!(root, event)
  end

  defp append_circuit_opened(root, service_id, opened_at) do
    event =
      Indexer.State.Event.new("services", "service.circuit_opened", "service:#{service_id}", %{
        service_id: service_id,
        opened_at: opened_at |> DateTime.truncate(:microsecond) |> DateTime.to_iso8601(),
        threshold: 1
      })

    Jsonl.append_event!(root, event)
  end

  defp tmp_dir do
    path =
      Path.join(
        System.tmp_dir!(),
        "indexer-service-runner-test-#{System.unique_integer([:positive])}"
      )

    File.rm_rf!(path)
    File.mkdir_p!(path)
    path
  end
end
