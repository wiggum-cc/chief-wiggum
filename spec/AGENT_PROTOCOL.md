# Agent Communication Protocol

Status: Draft v2

## Purpose

This protocol defines how Indexer communicates with external agent runtimes and
deterministic hooks. It replaces the v1 convention where agents communicated mostly
through files in worker directories.

SQLite is the primary communication and persistence channel. Files may still exist
as workspace content or artifacts, but they are no longer the orchestration contract.

## Communication Scopes

Indexer has four communication scopes:

1. **Runtime stream**
   - Raw stdout/stderr/app-server messages from an external agent runtime.
   - Stored in `agent_events.raw_payload`.
   - Normalized by runtime adapters.

2. **Normalized event stream**
   - Backend-independent agent events.
   - Stored in `agent_events.normalized_payload`.
   - Consumed by hooks, web UI, metrics, and pipeline gates.

3. **Context store**
   - Rendered prompts, summaries, reports, structured inputs, and extracted outputs.
   - Stored in `contexts` and `artifacts`.

4. **Effect outbox**
   - Durable requested side effects.
   - Stored in `effects`.
   - Executed by Indexer effect workers.

## Normalized Runtime Events

Each runtime adapter must convert backend-specific logs into normalized events.

Common event types:

- `session.started`
- `session.resumed`
- `turn.started`
- `turn.completed`
- `turn.failed`
- `message.delta`
- `message.completed`
- `tool.started`
- `tool.delta`
- `tool.completed`
- `tool.failed`
- `approval.requested`
- `approval.resolved`
- `usage.updated`
- `rate_limit.detected`
- `runtime.stderr`
- `runtime.stdout`
- `runtime.exited`

Event envelope:

```json
{
  "event_type": "tool.completed",
  "timestamp": "2026-05-07T12:00:00Z",
  "agent_run_id": "ar_123",
  "runtime": "codex",
  "session_id": "thread-1:turn-2",
  "sequence": 42,
  "payload": {},
  "usage": {},
  "raw_ref": "raw-event-id"
}
```

Adapters may emit runtime-specific payload fields, but dashboards and pipelines must
depend only on the normalized event envelope unless they explicitly opt into a
backend-specific contract.

## Runtime Invocation Input

Before launching an agent runtime, Indexer creates an invocation record:

```json
{
  "agent_run_id": "ar_123",
  "runtime": "codex",
  "mode": "app_server",
  "workspace": {
    "path": "/repo/.indexer/worktrees/TASK-001"
  },
  "objective": {
    "system_context_id": "ctx_sys",
    "user_context_id": "ctx_user",
    "rendered_text": "..."
  },
  "session": {
    "resume_session_id": null
  },
  "policy": {
    "approval_policy": "unless_trusted",
    "sandbox": "workspace_write",
    "network": false,
    "timeout_seconds": 10800
  },
  "runtime_config": {}
}
```

The adapter converts this record into the backend-specific process, app-server, or
SDK call.

## Runtime Completion

Runtime completion does not equal agent success. A runtime may finish cleanly while
the agent outcome is `needs_work`, `blocked`, or `inconclusive`.

The adapter records:

- process exit status,
- terminal runtime event,
- session/thread/turn ids,
- token or cost usage when available,
- raw logs,
- any backend error classification.

The agent's `extract_result` hook then creates the semantic `AgentResult`.

## Deterministic Hook Protocol

Hooks use JSON stdin/stdout. Hook processes must write diagnostics to stderr and
machine-readable output to stdout.

Hook output must be parseable JSON. Invalid JSON is a hard hook failure.

Hooks must not write directly to Indexer SQLite unless implemented as trusted Elixir
modules. External executable hooks communicate only through their output envelope.

## Artifacts

Artifacts are durable records linked to a work item, pipeline node, agent run, or
review. Supported storage kinds:

- `sqlite_text`
- `sqlite_json`
- `sqlite_blob`
- `workspace_file`
- `control_branch_file`
- `external_uri`

Artifacts have digests. Large raw logs may be stored compressed in SQLite or an
artifact file, but their index metadata remains in SQLite.

## Context Passing

Pipeline nodes pass data by writing context records and artifact references.

Context records are immutable. A later node may create a new context derived from
earlier contexts, but must not mutate prior records.

Common context scopes:

- `work_item`
- `pipeline`
- `node`
- `agent`
- `review`
- `repository`
- `control_branch`

## Follow-Up Work

Agents may propose follow-up work in `AgentResult.follow_up_work`. Indexer does not
blindly schedule it. A deterministic hook or operator policy decides whether to:

- discard,
- record as draft,
- create a new work item,
- attach as review comment,
- append to a backlog file on the control branch.

## Error Handling

All failures are classified into one of:

- `runtime_error`: external agent process/protocol failed.
- `model_error`: model completed but did not satisfy output contract.
- `hook_error`: deterministic hook failed.
- `policy_error`: approval/capability/sandbox violation.
- `workspace_error`: git or filesystem workspace failed.
- `effect_error`: requested effect failed.
- `operator_cancelled`: run cancelled by user or service policy.

Pipelines route on error class, outcome, and node metadata.
