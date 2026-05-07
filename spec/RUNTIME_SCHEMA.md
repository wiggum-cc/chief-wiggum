# Runtime Adapter Specification

Status: Draft v2
Target implementation: Elixir/OTP
Baseline: Chief Wiggum v1 runtime schema and `lib/runtime/*`

## Overview

The runtime layer is the backend-agnostic execution facade between Indexer agents
and external agent harnesses. It owns invocation, sessions, retries, rate limiting,
prompt wrapping, stream normalization, cancellation, and result text extraction.

Agents and pipelines must not know whether the active backend is Codex, Claude,
OpenCode, Pi, Hermes, PlotCode, ClockCode, or a custom harness. They depend only
on the runtime contract.

This preserves the v1 architecture:

```text
runtime facade
  -> backend selection
  -> backend argument/session construction
  -> retry wrapper
  -> backend invocation
  -> text/session extraction
  -> usage/rate-limit update
```

The v2 implementation expresses this as Elixir behaviours and supervised external
processes instead of sourced bash functions.

## Architecture

Logical module layout:

```text
lib/indexer/runtime/
  runtime.ex                  # Public facade and config resolution
  adapter.ex                  # Adapter behaviour
  invocation.ex               # AgentInvocation struct
  session.ex                  # RuntimeSession struct
  retry.ex                    # Retry/backoff policy
  prompts.ex                  # Prompt wrapper resolution
  stream.ex                   # Raw and normalized event streaming
  usage.ex                    # Usage/rate-limit contracts
  process_tree.ex             # Subprocess supervision/cancellation

lib/indexer/runtime/adapters/
  codex.ex
  claude.ex
  opencode.ex
  pi.ex
  hermes.ex
  plotcode.ex
  clockcode.ex
  custom.ex
```

Adapters may use:

- app-server style structured protocols,
- JSON/JSONL streaming CLIs,
- text-only CLIs,
- supervised service processes,
- SDK wrappers through ports or sidecar processes.

## Backend Selection

Runtime backend selection keeps v1's precedence model with v2 paths:

| Priority | Source | Example |
|----------|--------|---------|
| 1 | explicit pipeline/agent invocation override | `runtime.adapter = "codex"` |
| 2 | environment variable | `INDEXER_RUNTIME_BACKEND=opencode` |
| 3 | `.indexer/config.json` project override | `{ "runtime": { "backend": "opencode" } }` |
| 4 | control-branch project config | `config/runtime.json` on `indexer/control` |
| 5 | built-in config | `config/config.json` |
| 6 | default | implementation-defined, recommended `codex` when available |

Resolved backend config is copied into the `agent_runs.jsonl` start record.

## Public API

The v1 public API remains normative as logical operations.

### `runtime_init()`

Initialize runtime configuration, discover backends, validate adapter availability,
and load prompt wrapper config. The operation MUST be idempotent.

### `run_agent_once(workspace, system_prompt, user_prompt, output_ref, max_turns, session_id)`

Single-shot execution.

| Argument | Description |
|----------|-------------|
| `workspace` | Directory where the runtime should operate. |
| `system_prompt` | Rendered system prompt. |
| `user_prompt` | Rendered user prompt. |
| `output_ref` | Agent run or artifact ref where output is recorded. |
| `max_turns` | Runtime turn limit. |
| `session_id` | Optional existing or named session id. |

The runtime facade validates policy, applies prompt wrappers, launches the adapter,
streams events, and returns normalized completion metadata.

### `run_agent_once_with_session(workspace, system_prompt, user_prompt, output_ref, max_turns, session_id)`

Create a new named session and run one turn. Backends that do not support named
sessions must report unsupported capability before launch.

### `run_agent_resume(session_id, prompt, output_ref, max_turns)`

Resume a prior session with a new prompt. Used for summaries, backup result
extraction, continuation, and resume-mode agents.

### `run_ralph_loop(...)`

Iterative execution with summary carry-forward and optional supervisor checks.
See [Execution Patterns](#execution-patterns).

### `run_ralph_loop_supervised(...)`

Alias or wrapper for `run_ralph_loop` with a non-zero supervisor interval.

### `runtime_exec_with_retry(invocation)`

Retry-wrapped backend invocation. Retryability is delegated to the adapter and
policy is resolved by `Indexer.Runtime.Retry`.

## Adapter Behaviour

Every adapter MUST implement the following logical callbacks. Elixir function
names may differ, but the behaviour must cover this surface.

```elixir
@callback init(map()) :: {:ok, map()} | {:error, term()}
@callback validate_config(map()) :: :ok | {:error, term()}
@callback capabilities(map()) :: map()
@callback invoke(AgentInvocation.t()) ::
  {:ok, RuntimeSession.t()} | {:error, RuntimeError.t()}
@callback build_exec_args(AgentInvocation.t()) ::
  {:ok, [String.t()]} | {:error, term()}
@callback build_resume_args(RuntimeSession.t(), AgentInvocation.t()) ::
  {:ok, [String.t()]} | {:error, term()}
@callback classify_error(term(), map()) ::
  :retryable | :permanent | :operator_required
@callback extract_text(RuntimeArtifact.t()) :: {:ok, String.t()} | {:error, term()}
@callback extract_session_id(RuntimeArtifact.t()) ::
  {:ok, String.t() | nil} | {:error, term()}
@callback normalize_event(term()) ::
  {:ok, NormalizedRuntimeEvent.t()} | :ignore | {:error, term()}
```

Optional callbacks:

| Callback | Default | Purpose |
|----------|---------|---------|
| `supports_sessions?/1` | `false` | Whether resume/named sessions are supported. |
| `usage_update/2` | no-op | Persist usage metrics. |
| `rate_limit_check/1` | `:ok` | Check whether backend is currently rate limited. |
| `rate_limit_wait/1` | policy sleep | Wait or schedule retry. |
| `generate_session_id/1` | UUID | Generate session ids. |
| `backend_name/0` | adapter module name | Human-readable backend name. |
| `cancel_turn/2` | terminate process | Cooperative cancellation. |

## Runtime Modes

### `app_server`

Persistent subprocess or service process with structured messages. Codex App
Server is the reference pattern.

Properties:

- one long-lived runtime process per worker, runtime pool, or session,
- initialize/thread/turn operations,
- structured event stream,
- explicit cancellation when supported,
- strong session continuity.

### `cli_json_stream`

Process-per-run or process-per-turn command that emits JSON/JSONL.

Properties:

- adapter parses structured stream,
- sessions may be passed through CLI flags,
- tool calls, usage, and assistant messages are available if emitted.

### `cli_text`

Text-only command.

Properties:

- raw stdout/stderr are stored as artifacts,
- adapter may extract best-effort text,
- semantic results rely heavily on deterministic `extract_result` hooks,
- lower observability than structured modes.

### `sdk`

Adapter communicates with a language SDK through a supervised boundary such as a
port, sidecar process, or service process. Direct unbounded NIF-like execution is
not acceptable for long-running model calls because cancellation and crash
isolation must remain explicit.

## AgentInvocation

```json
{
  "agent_run_id": "agent_run_123",
  "agent_type": "engineering.software-engineer",
  "runtime": "codex",
  "mode": "app_server",
  "workspace_path": "/repo/.indexer/worktrees/worker-TASK-001-1/workspace",
  "objective": {
    "system": "...",
    "user": "...",
    "continuation": null,
    "output_schema": null
  },
  "session": {
    "resume": false,
    "runtime_session_id": null,
    "parent_session_id": null
  },
  "policy": {
    "approval_policy": "unless_trusted",
    "sandbox": "workspace_write",
    "writable_roots": [],
    "network": false,
    "timeout_seconds": 10800,
    "max_turns": 50
  },
  "runtime_config": {},
  "context": {},
  "artifacts": []
}
```

The invocation record is written or linked from `agent_runs.jsonl` before the
external runtime starts.

## RuntimeSession

```json
{
  "runtime": "codex",
  "mode": "app_server",
  "runtime_session_id": "thread_1",
  "current_turn_id": "turn_1",
  "os_pid": 12345,
  "status": "running",
  "started_at": "2026-05-07T12:00:00Z",
  "last_event_at": "2026-05-07T12:00:10Z",
  "supports_resume": true
}
```

Session records are linked to agent runs and runtime event streams. The adapter
owns mapping between Indexer session ids and backend session/thread ids.

## Execution Patterns

### Single Shot

```text
caller
  -> run_agent_once
    -> resolve backend
    -> apply prompt wrappers
    -> adapter.build_exec_args or structured app-server request
    -> runtime_exec_with_retry
      -> adapter.invoke
      -> adapter.classify_error on failure
    -> adapter.extract_text
    -> adapter.extract_session_id
    -> append completion records
```

### Iterative Loop (`ralph_loop`)

```text
run_ralph_loop
  -> adapter.rate_limit_check
  -> completion_check
  -> generate or resume session id
  -> work phase
       -> build user prompt from callback
       -> invoke backend
       -> stream events
  -> summary phase
       -> resume session when supported
       -> otherwise run fresh invocation with prior output as context
  -> supervisor phase every N iterations
       -> supervisor may CONTINUE, STOP, or RESTART
  -> sleep/backoff
```

This pattern is central to the product and should be preserved. It solves context
bloat by carrying forward summaries instead of blindly reusing all raw transcript
history.

### Session Resume

```text
caller
  -> run_agent_resume
    -> adapter.supports_sessions?
    -> adapter.build_resume_args or app-server turn request
    -> runtime_exec_with_retry
```

If sessions are unsupported, the runtime facade returns an unsupported capability
error. Callers may fall back to context summary plus fresh invocation.

### Backup Result Extraction

When result extraction returns `UNKNOWN`, the pipeline or agent result layer may
call `run_agent_resume` with a constrained prompt asking for one valid gate result.
The adapter does not decide the semantic value; it only provides resume and text
extraction.

## Retry Strategy

Retries use exponential backoff:

```text
delay = min(initial_backoff * multiplier^attempt, max_backoff)
```

Default parameters:

| Parameter | Default |
|-----------|---------|
| `max_retries` | `3` |
| `initial_backoff_ms` | `5000` |
| `max_backoff_ms` | `60000` |
| `backoff_multiplier` | `2` |

Config precedence:

1. invocation policy,
2. environment variables (`INDEXER_RUNTIME_*`),
3. project `.indexer/config.json`,
4. built-in backend config,
5. defaults.

Adapters classify errors:

| Class | Examples |
|-------|----------|
| `retryable` | transient network failure, rate limit, temporary service failure, process startup race. |
| `permanent` | missing executable, invalid config, unsupported runtime mode, auth impossible. |
| `operator_required` | approval required, quota exhausted, ambiguous auth state, policy conflict. |

Pipeline retry policy decides whether to retry a retryable runtime failure.

## Usage And Rate Limiting

The runtime facade provides generic hooks for usage and rate limiting. Adapters
provide backend-specific implementation.

| Operation | Purpose |
|-----------|---------|
| `usage_update` | Append usage/cost event. |
| `rate_limit_check` | Decide whether invocation can start. |
| `rate_limit_wait` | Sleep, schedule retry, or require operator action. |
| `cost_estimate` | Optional preflight estimate for budget checks. |

Usage events go to `agent_events.jsonl` or a runtime usage ledger if the
implementation separates it. Pipeline cost budget decisions are recorded with
pipeline node runs.

## Prompt Wrappers

Prompt wrappers are preserved from v1 and apply to work-phase invocations.

```json
{
  "runtime": {
    "backends": {
      "codex": {
        "prompts": {
          "pre_system": "",
          "post_system": "",
          "pre_user": "",
          "post_user": ""
        }
      }
    }
  }
}
```

Resolution priority:

| Priority | Source |
|----------|--------|
| 1 | environment variables such as `INDEXER_PROMPT_PRE_SYSTEM` |
| 2 | project `.indexer/config.json` |
| 3 | control-branch config |
| 4 | built-in config |
| 5 | empty default |

File references beginning with `@` are resolved relative to the Indexer config
root or the target project root according to config source.

Wrapping scope:

| Operation | System Wrapped | User Wrapped |
|-----------|----------------|--------------|
| `run_agent_once` | yes | yes |
| `run_agent_once_with_session` | yes | yes |
| `run_agent_resume` | no | yes |
| `run_ralph_loop` work phase | yes | yes |
| `run_ralph_loop` summary phase | no | no |
| `run_ralph_loop` supervisor phase | no | no |

## Logging And Event Normalization

Runtime logs are stored in two layers:

1. raw artifacts for exact backend output,
2. normalized JSONL events for generic Indexer consumers.

Adapters MUST record:

- process/app-server start,
- session/thread ids,
- turn ids,
- assistant messages or deltas,
- tool calls,
- approval requests,
- stdout/stderr diagnostics,
- usage,
- terminal status,
- process exit,
- error classification.

The adapter boundary is where backend-specific log formats are handled. Agents,
pipelines, services, and UI surfaces should consume normalized events.

## Adapter-Specific Notes

### Codex

Preferred mode: `app_server` when available.

The adapter should preserve logical fields:

- thread/session id,
- turn id,
- turn status,
- assistant text deltas,
- tool call start/completion,
- approval requests,
- usage,
- terminal error.

Fallback mode: CLI JSON stream or CLI text mode.

### Claude

Preferred mode: structured CLI stream.

The adapter owns:

- command construction,
- session/resume flags,
- stream parsing,
- text extraction,
- usage extraction,
- retry classification,
- approval/sandbox flags.

Claude-specific fields must remain behind the adapter boundary.

### OpenCode

The adapter discovers the executable, selects the best structured stream mode,
normalizes messages and sessions, and reports `supports_sessions: false` if the
installed version lacks resume semantics.

### Pi, Hermes, PlotCode, ClockCode

These adapters use the same contract. Each implementation must document:

- executable, app-server, or API entrypoint,
- session model,
- stream format,
- text extraction method,
- approval/sandbox behavior,
- retryable error patterns,
- capability support.

Until a structured stream exists, use `cli_text` plus deterministic
`extract_result` hooks.

### Custom

The custom adapter is configured by command templates or a module. It must still
produce normalized events and declare capabilities. It may be appropriate for
site-local harnesses.

## Cancellation

Cancellation is cooperative first and forceful second:

1. Ask runtime to cancel active turn if supported.
2. Terminate subprocess or app-server session.
3. Kill process tree after timeout.
4. Append runtime cancellation event.
5. Mark agent run cancelled or failed according to caller policy.
6. Let pipeline route from `operator_cancelled`, `timeout`, or configured result.

Cancellation must preserve raw logs and the current workspace unless cleanup
policy explicitly removes them through an effect.

## Security Boundary

Adapters translate Indexer policy into runtime-specific sandbox and approval
settings. They must not silently widen permissions.

If a runtime cannot satisfy requested policy, the adapter fails before launch.

Policy includes:

- workspace path,
- writable roots,
- network access,
- approval behavior,
- secret access,
- shell/tool access,
- timeout,
- model/tool capabilities.

## Capability Matrix

Every adapter reports capabilities at runtime:

| Capability | Meaning |
|------------|---------|
| `sessions` | Can resume prior sessions. |
| `named_sessions` | Can create caller-specified session ids. |
| `structured_stream` | Emits machine-readable events. |
| `tool_events` | Emits tool call start/completion events. |
| `usage` | Reports token/cost usage. |
| `approvals` | Supports approval request events. |
| `sandbox_workspace_write` | Can enforce workspace-write policy. |
| `sandbox_readonly` | Can enforce readonly policy. |
| `cancel_turn` | Supports cooperative turn cancellation. |

Validation compares agent/pipeline policy with adapter capabilities before launch.

## Writing A New Adapter

1. Implement the adapter behaviour.
2. Declare capabilities.
3. Add config schema for the adapter.
4. Normalize runtime events.
5. Implement retry classification.
6. Implement text and session extraction.
7. Add tests for one-shot, resume, cancellation, retry, and log normalization.

Adapters are the only place where backend-specific protocol details belong.
