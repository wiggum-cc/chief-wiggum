# Agent Communication Protocol

Status: Draft v2
Target implementation: Elixir/OTP
Baseline: Chief Wiggum v1 inter-agent communication protocol

## Overview

Agents operate in isolated worker directories but must share results, context,
progress, checkpoints, review comments, and workspace state. V1 achieved this
through worker files, epoch-named result JSON, reports, summaries, activity logs,
checkpoints, kanban markers, and shared git worktrees.

Indexer preserves those communication patterns but changes the authoritative
channel:

- append-only JSONL ledgers are the source of truth,
- worker files are artifacts, projections, or workspace content,
- backend-specific logs are normalized through runtime adapters,
- side effects flow through the effect outbox.

There is still no message broker requirement. The core remains portable: POSIX
filesystem, git, JSONL, and supervised local processes.

## Communication Scopes

Indexer defines these scopes:

| Scope | Purpose | Primary Ledger |
|-------|---------|----------------|
| Pipeline-local | Parent/previous/next step context and gate results. | `pipeline_node_runs.jsonl` |
| Agent-local | Agent run lifecycle, extracted result, outputs. | `agent_runs.jsonl` |
| Runtime stream | Raw and normalized backend events. | `agent_events.jsonl` |
| Context | Rendered prompts, summaries, memory, reports. | `contexts.jsonl` |
| Artifacts | Large logs, markdown reports, exported files. | `artifacts.jsonl` |
| Worker/work item | Worker lifecycle, work item status, leases. | `workers.jsonl`, `work_items.jsonl` |
| Change set | Git branch, review, merge, conflict state. | `change_sets.jsonl`, `reviews.jsonl`, `review_comments.jsonl` |
| Effects | Requested side effects and execution status. | `effects.jsonl` |

All records share the JSONL event envelope defined in `ARCHITECTURE.md`.

## Sequential Communication

Sequential communication passes information from one pipeline step to the next.
The five v1 mechanisms remain, translated to structured records.

| # | Mechanism | V1 Form | V2 Form |
|---|-----------|---------|---------|
| 1 | Gate result | `results/<epoch>-<agent>-result.json` with `outputs.gate_result` | `agent_runs.jsonl` completion record linked to `pipeline_node_runs.jsonl`. |
| 2 | Step enablement | `enabled_by` environment variable | `enabled_by` resolved from config/env/context projection and recorded as skipped or runnable. |
| 3 | Context inheritance | exported shell variables | structured context keys rendered into prompts and hook envelopes. |
| 4 | Git state globals | shell globals such as branch, PR URL, checkpoint sha | `change_sets.jsonl`, `workers.jsonl`, and `effects.jsonl` records. |
| 5 | Fix-retry loop | parent result -> inline fix agent -> parent re-run | `on_result` inline handler node runs linked to parent node run. |

### Gate Result Records

Every step's agent run must produce a semantic result:

```json
{
  "type": "agent.completed",
  "aggregate_id": "agent_run_123",
  "payload": {
    "agent_type": "engineering.security-audit",
    "pipeline_run_id": "pipeline_run_1",
    "node_run_id": "node_run_7",
    "status": "partial",
    "exit_code": 0,
    "outputs": {
      "gate_result": "FIX"
    },
    "artifacts": [
      {"artifact_id": "artifact_report_1", "kind": "report"}
    ]
  }
}
```

The pipeline engine reads the projected latest result for its node run. It must
not inspect raw runtime logs for routing except through the configured result
extraction hook.

### Step Enablement

`enabled_by` remains part of the pipeline schema. A step with false enablement:

- is skipped before visit count increments,
- writes a `pipeline.node.skipped` record,
- routes to `next`,
- does not run hooks or agent runtime.

Enablement may be resolved from:

- environment variables,
- project config,
- work item fields,
- control-branch config,
- runtime mode flags.

The resolved value and source are recorded for debugging.

### Context Inheritance

The v1 environment variables become context keys:

| Context Key | Description |
|-------------|-------------|
| `pipeline.parent.step_id` | Previous step id. |
| `pipeline.parent.node_run_id` | Previous node run id. |
| `pipeline.parent.agent_run_id` | Previous agent run id. |
| `pipeline.parent.session_id` | Previous runtime session id. |
| `pipeline.parent.result` | Previous gate result. |
| `pipeline.parent.report` | Previous report artifact id or exported path. |
| `pipeline.next.step_id` | Next step id when known. |
| `pipeline.current.step_id` | Current step id. |

External executable hooks and external agent harnesses may receive environment
variables derived from these keys, but the structured context is authoritative.

### Git State Communication

V1 used shell globals for branch names, safety checkpoint SHAs, and hosted forge
URLs. Indexer records git state as structured change-set and effect records:

```json
{
  "type": "change_set.updated",
  "aggregate_id": "change_set_123",
  "payload": {
    "work_item_id": "TASK-001",
    "worker_id": "worker_TASK_001_1",
    "target_ref": "refs/heads/main",
    "work_branch": "indexer/work/TASK-001/1",
    "base_sha": "abc123",
    "head_sha": "def456",
    "affected_files": ["lib/example.ex"],
    "status": "pending_review"
  }
}
```

Hosted forge URLs, if produced by an optional adapter, are metadata and not core
pipeline state.

## Arbitrary Communication

Arbitrary communication lets any agent read outputs from any other relevant agent.
The seven v1 mechanisms remain as logical APIs.

| # | Mechanism | V1 Form | V2 Form |
|---|-----------|---------|---------|
| 1 | `agent_comm_*` interface | path resolver in `agent-base.sh` | `Indexer.AgentComm` query API plus hook envelope context. |
| 2 | Result reads by agent name | latest result file lookup | projection query over `agent_runs.jsonl`. |
| 3 | Shared workspace | `worker_dir/workspace` | worker git worktree under `.indexer/worktrees/.../workspace`. |
| 4 | Activity log | `.ralph/logs/activity.jsonl` | normalized JSONL ledgers, especially `agent_events.jsonl` and `workers.jsonl`. |
| 5 | Checkpoints | `checkpoints/checkpoint-N.json` | checkpoint context records and optional exported artifacts. |
| 6 | Kanban status | `.ralph/kanban.md` markers | `work_items.jsonl` and control-branch work item records. |
| 7 | Reports, summaries, logs | worker directories | artifacts and context records with optional exported files. |

## Agent Communication API

The API should support the same lookup classes as v1:

| Operation | Returns |
|-----------|---------|
| `latest_result(worker_id, agent_type)` | Latest gate result and result metadata for an agent type. |
| `latest_report(worker_id, agent_type)` | Latest report artifact. |
| `latest_summary(worker_id, agent_type)` | Latest summary context or artifact. |
| `comments(change_set_id)` | Review comments linked to a change set. |
| `work_item(work_item_id)` | Work item title, body, status, dependencies. |
| `workspace(worker_id)` | Assigned workspace path and policy. |
| `context(scope, key)` | Context section by scope/key. |
| `artifact(artifact_id)` | Artifact metadata and storage ref. |

External hooks receive a subset of this data in their input envelope. Model-facing
agents receive rendered markdown context prepared by deterministic hooks.

## Worker Directory Structure

The worker directory remains the namespace boundary:

```text
.indexer/worktrees/worker-TASK-001-1/
├── workspace/                  # Git worktree
├── work_item.md                # Optional rendered work item artifact
├── live_sessions/              # Optional runtime session projections
├── logs/                       # Exported raw logs, not authoritative
├── results/                    # Exported result JSON, not authoritative
├── reports/                    # Exported markdown reports
├── summaries/                  # Exported summaries
├── checkpoints/                # Exported checkpoints
└── output/
    └── <agent-type>/
```

Naming convention for exported result/report artifacts should preserve the v1
epoch style for human scanning:

```text
results/<epoch>-<agent-type>-result.json
reports/<epoch>-<agent-type>-report.md
```

These exports are derived artifacts. JSONL records are the durable contract.

## Runtime Event Communication

Each runtime adapter converts backend-specific output into normalized events:

```json
{
  "type": "agent.runtime_event",
  "aggregate_id": "agent_run_123",
  "payload": {
    "runtime": "codex",
    "session_id": "thread_1",
    "turn_id": "turn_2",
    "sequence": 42,
    "event_type": "tool.completed",
    "payload": {},
    "usage": {},
    "raw_artifact_id": "artifact_raw_9"
  }
}
```

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
- `runtime.stdout`
- `runtime.stderr`
- `runtime.exited`

Pipelines and dashboards depend on normalized event fields. Backend-specific
payload fields may be preserved but must not leak into generic pipeline logic.

## Result Communication

### Writing Results

Agents and hooks do not mutate previous results. They append completion records.

Logical operation:

```text
write_result(agent_run_id, gate_result, extra_outputs, errors, artifacts)
```

Required behavior:

- map `gate_result` to status and exit code,
- validate against agent `valid_results` or declared mappings,
- append an `agent.completed` or `agent.failed` record,
- link artifacts and effects,
- update projections.

### Reading Results

Logical operations:

```text
read_subagent_result(worker_id, agent_type)
find_latest_result(worker_id, agent_type)
find_latest_report(worker_id, agent_type)
```

Reads are projection queries over ledgers. If projections are unavailable,
Indexer must replay the relevant JSONL stream.

## Progress Communication

### Iteration Summaries

Ralph-loop style agents produce iteration summaries as context records:

```json
{
  "type": "context.created",
  "aggregate_id": "agent_run_123",
  "payload": {
    "scope": "agent_iteration",
    "key": "summary",
    "iteration": 3,
    "format": "markdown",
    "content_ref": "artifact_summary_3",
    "summary": {
      "completed": ["Implemented authentication endpoint"],
      "in_progress": ["Writing unit tests"],
      "blocked": [],
      "next_steps": ["Complete tests", "Update docs"]
    }
  }
}
```

The compact prose summary is used as model context for later iterations.

### Structured Checkpoints

Checkpoint records preserve the v1 fields:

```json
{
  "version": "2.0",
  "iteration": 3,
  "session_id": "session_abc",
  "status": "in_progress",
  "files_modified": ["src/auth/handler.ts"],
  "completed_tasks": ["Implement auth endpoint"],
  "next_steps": ["Write unit tests"],
  "prose_summary": "..."
}
```

Checkpoints are written as context records and may be exported to
`checkpoints/checkpoint-N.json`.

## Sub-Agent Invocation

Sub-agent invocation preserves the v1 parent-to-child pattern:

```text
parent agent
  -> run sub-agent engineering.validation-review
  -> read sub-agent gate result
  -> continue, fix, or fail
```

V2 requirements:

- sub-agent runs have their own `agent_run_id`,
- `parent_agent_run_id` links child to parent,
- sub-agents share the worker workspace unless a pipeline explicitly creates a
  new scoped workspace,
- sub-agents must not own worker lifecycle state,
- sub-agent results are visible to all later steps through `AgentComm`.

## Work Item And Status Communication

V1 kanban markers become structured statuses. The status categories are preserved:

| V1 Marker | V2 Status | Satisfies Dependencies |
|-----------|-----------|------------------------|
| `[ ]` | `pending` | no |
| `[=]` | `in_progress` | no |
| `[P]` | `pending_review` | no |
| `[x]` | `merged` | yes |
| `[*]` | `failed` | no |
| `[N]` | `not_planned` | no |

Only `merged` satisfies dependencies. `pending_review` does not.

Status changes append records to `work_items.jsonl` and may be mirrored to the
git control branch.

## File Locking And Append Safety

JSONL ledgers require append safety:

- one complete JSON object per line,
- newline-terminated records,
- per-ledger append lock,
- `fsync` policy configurable by durability mode,
- recovery truncates to the last complete newline,
- projections are rebuilt after suspected corruption.

Shared non-ledger resources still use locks:

| Resource | Lock Scope |
|----------|------------|
| JSONL ledger | per ledger file |
| worktree | per worker/worktree |
| control branch checkout | per repository control branch |
| effect idempotency key | per effect key |
| runtime session | per runtime session id |

## Workspace Boundary Protocol

Agents may only write inside their assigned workspace unless they are writing
through Indexer APIs to state ledgers or artifact storage.

Violation detection checks:

- writes outside the assigned workspace,
- destructive git operations in the target repository,
- direct writes to `.indexer/state` by untrusted external hooks,
- modification of control-branch checkout outside the effect executor,
- readonly step workspace mutations.

On violation:

1. cancel the runtime turn,
2. terminate or quarantine the hook/process,
3. append a `workspace.violation` event,
4. mark the node failed,
5. route through the pipeline failure policy,
6. preserve logs and workspace for inspection unless cleanup policy says otherwise.

## Follow-Up Work

Agents may propose follow-up work in their result outputs. Indexer must not blindly
schedule it. A deterministic hook or operator policy decides whether to:

- discard it,
- record it as a draft work item,
- append it to backlog records on the control branch,
- attach it as a review comment,
- schedule it immediately.

Follow-up creation is an effect because it changes shared work state.

## Error Classes

All failures are normalized:

| Error Class | Meaning |
|-------------|---------|
| `runtime_error` | External runtime process/protocol failed. |
| `model_error` | Model completed but violated output contract. |
| `hook_error` | Deterministic hook failed. |
| `policy_error` | Capability, approval, or sandbox policy failed. |
| `workspace_error` | Workspace or git operation failed. |
| `effect_error` | Requested effect failed. |
| `operator_cancelled` | User or service policy cancelled the run. |

Pipelines may route on gate result, error class, or both.

## Best Practices

- Treat ledgers as the contract and exported files as convenience artifacts.
- Keep model-facing context compact and generated by deterministic hooks.
- Keep result values explicit and declared.
- Use artifact ids instead of raw paths when passing reports between agents.
- Write checkpoints and summaries often enough for useful resume.
- Do not hide git/control-branch side effects inside model instructions.
- Preserve worker directory isolation.
