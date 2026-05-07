# Runtime Adapter Specification

Status: Draft v2

## Purpose

Runtime adapters connect Indexer to external agent harnesses. Each harness has its
own invocation style, session model, log stream, approval behavior, and output shape.
The adapter layer owns those differences.

Supported v2 adapter targets:

- `codex`
- `claude`
- `opencode`
- `pi`
- `custom`

## Adapter Responsibilities

Every adapter must implement:

- Validate runtime availability and authentication.
- Convert an `AgentInvocation` record into a process, app-server, SDK, or command.
- Stream raw runtime output into SQLite.
- Normalize backend-specific events into `agent_events`.
- Track sessions, turns, approvals, tool calls, usage, and terminal status.
- Classify retryable vs permanent runtime failures.
- Support cancellation and timeout.
- Expose runtime capabilities to agent and pipeline validation.

## Adapter Behaviour

Elixir behaviour shape:

```elixir
@callback validate_config(map()) :: :ok | {:error, term()}
@callback capabilities(map()) :: map()
@callback start_session(AgentInvocation.t()) :: {:ok, RuntimeSession.t()} | {:error, term()}
@callback start_turn(RuntimeSession.t(), AgentInvocation.t()) :: {:ok, TurnRef.t()} | {:error, term()}
@callback stream(RuntimeSession.t(), function()) :: :ok | {:error, term()}
@callback cancel(RuntimeSession.t()) :: :ok | {:error, term()}
@callback classify_error(term()) :: :retryable | :permanent | :operator_required
@callback normalize_event(term()) :: {:ok, NormalizedEvent.t()} | :ignore | {:error, term()}
```

Adapters may implement a simpler one-shot mode if the runtime has no persistent
session protocol.

## Runtime Modes

### `app_server`

A persistent subprocess speaks a structured line-delimited protocol over stdio.
Codex App Server is the reference target for this mode.

Properties:

- Starts one long-lived runtime process per worker or session pool.
- Sends initialize/thread/turn messages.
- Streams structured events.
- Supports continuation turns in the same thread when available.
- Can expose dynamic tools without leaking host secrets to the model runtime.

### `cli_json_stream`

A command emits JSON or JSONL events for a single run.

Properties:

- Process-per-turn or process-per-agent-run.
- Session resume may be supported through CLI flags.
- Adapter parses JSON stream and maps backend fields to normalized events.

### `cli_text`

A command emits mostly text logs.

Properties:

- Adapter stores raw stdout/stderr.
- Result extraction relies on deterministic hooks or structured output files.
- Lower fidelity than structured modes.

### `sdk`

An adapter calls a language SDK directly from Elixir through a port, NIF boundary,
or service process. This is allowed only if process supervision and cancellation
semantics remain explicit.

## AgentInvocation

```json
{
  "agent_run_id": "ar_123",
  "agent_id": "engineering.implementation",
  "runtime": "codex",
  "mode": "app_server",
  "workspace_path": "/repo/.indexer/worktrees/TASK-001",
  "objective": {
    "system": "...",
    "user": "...",
    "continuation": null,
    "output_schema": null
  },
  "session": {
    "resume": false,
    "runtime_session_id": null
  },
  "policy": {
    "approval_policy": "unless_trusted",
    "sandbox": "workspace_write",
    "writable_roots": [],
    "network": false,
    "timeout_seconds": 10800
  },
  "runtime_config": {}
}
```

## Normalized RuntimeSession

```json
{
  "runtime": "codex",
  "mode": "app_server",
  "pid": 12345,
  "runtime_session_id": "thread-1",
  "current_turn_id": "turn-1",
  "status": "running",
  "started_at": "2026-05-07T12:00:00Z"
}
```

## Codex Adapter

Preferred mode: `app_server`.

The Codex adapter should use Codex App Server when available because it provides
structured thread/turn control and streamable events. The adapter must tolerate
compatible payload shape changes by mapping logical fields rather than relying on
incidental field ordering.

Required logical fields:

- thread/session id,
- turn id,
- turn status,
- assistant message deltas,
- tool call start/completion,
- approval requests,
- usage,
- terminal error.

Fallback mode: Codex CLI non-interactive execution with JSON stream.

## Claude Adapter

Preferred mode: structured CLI stream if available.

The Claude adapter owns:

- command construction,
- session/resume flags,
- stream-json parsing,
- text extraction,
- usage extraction,
- retry classification,
- approval/sandbox flags.

Claude-specific event fields must remain behind the adapter boundary.

## OpenCode Adapter

OpenCode support follows the same contract:

- discover executable,
- choose best structured stream mode available,
- normalize sessions and messages,
- classify retryable failures,
- expose declared capabilities.

If OpenCode lacks a session feature, the adapter reports `supports_sessions: false`
and Indexer uses context compaction plus fresh invocations.

## Pi Adapter

Pi support is defined through the generic adapter contract. The implementation must
document:

- executable or API entrypoint,
- session model,
- stream format,
- result extraction method,
- approval/sandbox behavior,
- retryable error patterns.

Until a structured Pi stream is available, use `cli_text` plus deterministic
`extract_result` hooks.

## Logging

Runtime logs are not files as protocol. They are database events.

The adapter records:

- raw chunks,
- normalized events,
- stderr diagnostics,
- process exit,
- token/cost usage,
- approval requests,
- tool calls,
- session metadata.

Optional artifact files may be written for large log exports, but SQLite metadata
must remain complete.

## Cancellation

Cancellation must be cooperative first and forceful second:

1. Ask runtime to cancel active turn if supported.
2. Terminate subprocess.
3. Kill process tree after timeout.
4. Mark runtime session cancelled.
5. Let pipeline route from `operator_cancelled` or policy cancellation.

## Retry Classification

Adapters classify runtime failures as:

- `retryable`: transient network, rate limit, process timeout, temporary service
  errors.
- `permanent`: invalid config, missing executable, authentication failure, unsupported
  runtime mode.
- `operator_required`: approval needed, policy conflict, exhausted quota, unknown
  authentication state.

Pipeline retry policy decides whether to retry.

## Security Boundary

Adapters are responsible for translating Indexer policy into runtime-specific
approval and sandbox settings. The adapter must not silently widen permissions.
If a runtime cannot satisfy a requested policy, invocation fails before launching.
