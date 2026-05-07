defmodule Indexer.Runtime.ExecutableTest do
  use ExUnit.Case, async: true

  alias Indexer.Runtime
  alias Indexer.Runtime.Invocation
  alias Indexer.Runtime.Session
  alias Indexer.State.Jsonl

  defmodule RetryAdapter do
    @behaviour Indexer.Runtime.Adapter

    @impl true
    def init(config), do: {:ok, config}

    @impl true
    def validate_config(_config), do: :ok

    @impl true
    def capabilities(_config), do: %{}

    @impl true
    def invoke(invocation) do
      attempt = Process.get(:runtime_retry_attempt, 0)
      Process.put(:runtime_retry_attempt, attempt + 1)

      if attempt == 0 do
        {:error, :timeout}
      else
        {:ok,
         %Session{
           runtime: invocation.runtime,
           mode: invocation.mode,
           runtime_session_id: "session-retry",
           status: "completed",
           started_at:
             DateTime.utc_now() |> DateTime.truncate(:microsecond) |> DateTime.to_iso8601(),
           text: "<result>PASS</result>",
           events: []
         }}
      end
    end

    @impl true
    def build_exec_args(_invocation), do: {:ok, []}

    @impl true
    def build_resume_args(_session, _invocation), do: {:ok, []}

    @impl true
    def classify_error(:timeout, _config), do: :retryable
    def classify_error(_reason, _config), do: :permanent

    @impl true
    def extract_text(session), do: {:ok, session.text}

    @impl true
    def extract_session_id(session), do: {:ok, session.runtime_session_id}

    @impl true
    def normalize_event(_event), do: :ignore

    @impl true
    def supports_sessions?(_config), do: false

    @impl true
    def usage_update(_usage, _config), do: :ok

    @impl true
    def rate_limit_check(_config), do: :ok

    @impl true
    def rate_limit_wait(_config), do: :ok

    @impl true
    def generate_session_id(_config), do: "session"

    @impl true
    def backend_name, do: "retry"

    @impl true
    def cancel_turn(_session, _config), do: {:error, :unsupported}
  end

  test "invokes an executable adapter and records normalized runtime events" do
    root = tmp_dir()

    stdout =
      JSON.encode!(%{
        text: "<result>PASS</result>",
        session_id: "session-1",
        turn_id: "turn-1",
        events: [
          %{event_type: "message.completed", payload: %{text: "done"}}
        ]
      })

    invocation =
      invocation(%{
        runtime_config: %{"command" => ["printf", "%s", stdout], "timeout_seconds" => 5}
      })

    assert {:ok, result} = Runtime.invoke(root, invocation)
    assert result.text == "<result>PASS</result>"
    assert result.session.runtime_session_id == "session-1"
    assert [_event] = result.events

    events = root |> Jsonl.ledger_path("agent_events") |> Jsonl.read!()
    assert Enum.any?(events, &(&1["type"] == "runtime.invocation.started"))
    assert Enum.any?(events, &(&1["type"] == "agent.runtime_event"))
    assert Enum.any?(events, &(&1["type"] == "runtime.invocation.completed"))
  end

  test "retries retryable runtime failures within attempt budget" do
    root = tmp_dir()
    Process.delete(:runtime_retry_attempt)

    assert {:ok, result} =
             Runtime.invoke(root, invocation(%{runtime: "retry"}),
               adapter: RetryAdapter,
               max_attempts: 2
             )

    assert result.text == "<result>PASS</result>"
    assert result.session.runtime_session_id == "session-retry"

    events = root |> Jsonl.ledger_path("agent_events") |> Jsonl.read!()
    assert Enum.count(events, &(&1["type"] == "runtime.invocation.started")) == 2
    assert Enum.any?(events, &(&1["type"] == "runtime.invocation.failed"))
    assert Enum.any?(events, &(&1["type"] == "runtime.invocation.retry_scheduled"))
    assert Enum.any?(events, &(&1["type"] == "runtime.invocation.completed"))
  end

  defp invocation(overrides) do
    defaults = %{
      agent_run_id: "agent-run-1",
      agent_type: "test.pass",
      runtime: "codex",
      mode: "cli_text",
      workspace_path: File.cwd!(),
      objective: %{"system" => "system", "user" => "user"},
      policy: %{"timeout_seconds" => 5, "max_turns" => 1},
      runtime_config: %{},
      context: %{"pipeline_run_id" => "pipeline-run-1"},
      artifacts: []
    }

    struct!(Invocation, Map.merge(defaults, overrides))
  end

  defp tmp_dir do
    path =
      Path.join(System.tmp_dir!(), "indexer-runtime-test-#{System.unique_integer([:positive])}")

    File.rm_rf!(path)
    File.mkdir_p!(path)
    path
  end
end
