defmodule Indexer.Runtime do
  @moduledoc """
  Runtime facade for external agent harnesses.

  Pipelines and agents call this module instead of directly invoking Codex,
  Claude, OpenCode, Pi, Hermes, PlotCode, ClockCode, or site-local harnesses.
  The facade resolves the adapter, records normalized runtime events, and returns
  backend-independent text/session metadata to the agent runner.
  """

  alias Indexer.Runtime.{Invocation, NormalizedEvent, Session}
  alias Indexer.State.{Event, Jsonl}

  @executable_adapter Indexer.Runtime.Adapters.Executable

  @builtin_adapters %{
    "codex" => @executable_adapter,
    "claude" => @executable_adapter,
    "opencode" => @executable_adapter,
    "pi" => @executable_adapter,
    "hermes" => @executable_adapter,
    "plotcode" => @executable_adapter,
    "clockcode" => @executable_adapter,
    "custom" => @executable_adapter,
    "executable" => @executable_adapter
  }

  @type invoke_result :: %{
          required(:session) => Session.t(),
          required(:text) => String.t(),
          required(:events) => [map()]
        }

  @doc """
  Invokes the runtime adapter for a normalized invocation.
  """
  @spec invoke(Path.t(), Invocation.t(), keyword()) :: {:ok, invoke_result()} | {:error, term()}
  def invoke(project_root, %Invocation{} = invocation, opts \\ []) when is_binary(project_root) do
    with {:ok, adapter} <- resolve_adapter(invocation.runtime, opts),
         :ok <- adapter.validate_config(invocation.runtime_config),
         :ok <- maybe_rate_limit_check(adapter, invocation.runtime_config) do
      max_attempts =
        opts
        |> Keyword.get(:max_attempts, Map.get(invocation.runtime_config, "max_attempts", 1))
        |> positive_attempts()

      invoke_with_retry(project_root, adapter, invocation, max_attempts, 0)
    end
  end

  @doc """
  Resolves a runtime adapter name to a module.

  Callers may pass `:adapters` as a map to override or extend the built-in
  registry, or `:adapter` to force a specific module in tests or site-local code.
  """
  @spec resolve_adapter(String.t(), keyword()) :: {:ok, module()} | {:error, term()}
  def resolve_adapter(name, opts) do
    case Keyword.get(opts, :adapter) do
      nil -> :not_forced
      module when is_atom(module) -> {:ok, module}
    end
    |> case do
      :not_forced -> resolve_named_adapter(name, opts)
      result -> result
    end
  end

  defp resolve_named_adapter(name, opts) do
    name = to_string(name)
    registry = Map.merge(@builtin_adapters, Keyword.get(opts, :adapters, %{}))

    case Map.fetch(registry, name) do
      {:ok, module} -> {:ok, module}
      :error -> {:error, {:unknown_runtime_adapter, name}}
    end
  end

  defp maybe_rate_limit_check(adapter, config) do
    if function_exported?(adapter, :rate_limit_check, 1) do
      adapter.rate_limit_check(config)
    else
      :ok
    end
  end

  defp positive_attempts(value) when is_integer(value) and value > 0, do: value
  defp positive_attempts(_value), do: 1

  defp invoke_with_retry(project_root, adapter, invocation, max_attempts, attempt) do
    append_runtime_event(project_root, invocation, "runtime.invocation.started", %{
      "runtime" => invocation.runtime,
      "mode" => invocation.mode,
      "attempt" => attempt
    })

    case adapter.invoke(invocation) do
      {:ok, %Session{} = session} ->
        normalized_events =
          append_adapter_events(project_root, invocation, adapter, session.events)

        text = extract_text!(adapter, session)

        append_runtime_event(project_root, invocation, "runtime.invocation.completed", %{
          "runtime" => invocation.runtime,
          "mode" => invocation.mode,
          "attempt" => attempt,
          "runtime_session_id" => session.runtime_session_id,
          "status" => session.status
        })

        {:ok, %{session: session, text: text, events: normalized_events}}

      {:error, reason} ->
        class = adapter.classify_error(reason, invocation.runtime_config)

        append_runtime_event(project_root, invocation, "runtime.invocation.failed", %{
          "runtime" => invocation.runtime,
          "mode" => invocation.mode,
          "attempt" => attempt,
          "error_class" => to_string(class),
          "reason" => inspect(reason)
        })

        if class == :retryable and attempt + 1 < max_attempts do
          append_runtime_event(project_root, invocation, "runtime.invocation.retry_scheduled", %{
            "runtime" => invocation.runtime,
            "mode" => invocation.mode,
            "attempt" => attempt,
            "next_attempt" => attempt + 1
          })

          invoke_with_retry(project_root, adapter, invocation, max_attempts, attempt + 1)
        else
          {:error, %{class: class, reason: reason}}
        end
    end
  end

  defp append_adapter_events(project_root, invocation, adapter, events) do
    events
    |> List.wrap()
    |> Enum.with_index(1)
    |> Enum.flat_map(fn {raw, sequence} ->
      case adapter.normalize_event(raw) do
        {:ok, %NormalizedEvent{} = event} ->
          [
            event
            |> Map.from_struct()
            |> append_normalized_event(project_root, invocation, sequence)
          ]

        {:ok, %{} = event} ->
          [append_normalized_event(event, project_root, invocation, sequence)]

        :ignore ->
          []

        {:error, reason} ->
          [
            append_normalized_event(
              %{
                "event_type" => "runtime.event_normalization_failed",
                "payload" => %{"reason" => inspect(reason), "raw" => inspect(raw)}
              },
              project_root,
              invocation,
              sequence
            )
          ]
      end
    end)
  end

  defp append_normalized_event(event, project_root, invocation, fallback_sequence) do
    event = Indexer.State.Json.normalize(event)

    payload =
      %{
        "agent_run_id" => invocation.agent_run_id,
        "runtime" => Map.get(event, "runtime", invocation.runtime),
        "session_id" => Map.get(event, "session_id"),
        "turn_id" => Map.get(event, "turn_id"),
        "sequence" => Map.get(event, "sequence", fallback_sequence),
        "event_type" => Map.get(event, "event_type", "runtime.event"),
        "payload" => Map.get(event, "payload", %{}),
        "usage" => Map.get(event, "usage", %{}),
        "raw_ref" => Map.get(event, "raw_ref")
      }

    append_runtime_event(project_root, invocation, "agent.runtime_event", payload)
  end

  defp append_runtime_event(project_root, invocation, type, payload) do
    event =
      Event.new("agent_events", type, invocation.agent_run_id, payload,
        actor: %{"type" => "runtime", "id" => invocation.runtime},
        correlation_id: Map.get(invocation.context, "pipeline_run_id")
      )

    Jsonl.append_event!(project_root, event)
  end

  defp extract_text!(adapter, session) do
    case adapter.extract_text(session) do
      {:ok, text} when is_binary(text) -> text
      {:error, _reason} -> ""
    end
  end
end
