# Indexer Architecture Specification

Status: Draft v2
Target implementation: Elixir/OTP
Baseline: Chief Wiggum v1 architecture, pipeline, runtime, service scheduler, and TLA models

## Overview

Indexer is the Elixir rewrite of the Chief Wiggum orchestration model. It keeps the
core v1 ideas:

- a task/work-item source,
- isolated git worktrees,
- workers that execute configurable pipelines,
- agents that are invoked through a backend-agnostic runtime,
- result-driven pipeline routing with fix loops,
- a service scheduler that drives orchestration responsibilities,
- crash-safe lifecycle transitions using an effect outbox.

Indexer deliberately changes three platform assumptions:

1. Durable orchestration state is append-only JSONL, not mutable shell globals
   or ad hoc status files.
2. The collaboration surface is a git control branch, not GitHub Issues or Pull
   Requests.
3. The implementation substrate is Elixir/OTP supervision, not bash process
   sourcing and Python bridge processes.

Indexer is not an agent harness. It prepares context, invokes external agent
harnesses, normalizes their events, runs deterministic hooks, and advances workflow
state. Codex, Claude, OpenCode, Pi, and future runtimes remain external.

## Preserved V1 Design Points

These v1 definitions remain part of the v2 design unless explicitly superseded:

- Pipeline as a bounded jump-based state machine.
- Ordered `steps` array with `id`, `agent`, `max`, `on_max`, `on_result`,
  `readonly`, `enabled_by`, `commit_after`, `config`, and `hooks`.
- Result mappings with `status`, `exit_code`, and `default_jump`.
- Standard gate results: `PASS`, `FAIL`, `FIX`, `SKIP`, plus `UNKNOWN` handling.
- Inline agent handlers for remediation loops.
- Markdown agents with frontmatter and tagged prompt sections.
- Shell-style deterministic extensions, generalized to executable hooks.
- Runtime backend interface: build exec args, build resume args, invoke, extract
  text/session id, classify retryability, usage/rate-limit hooks.
- Ralph-loop execution pattern: work phase, summary phase, optional supervisor
  phase, continuation context.
- Worker lifecycle states and events from `config/worker-lifecycle.json`.
- Effect outbox ordering and replay semantics from `formal/EffectOutbox.tla`.
- Scheduler priority terms from `formal/Scheduler.tla`.
- Service scheduler phases, schedule types, execution types, conditions, circuit
  breakers, health checks, and run modes.

## Intentional Deviations

| Area | V1 | V2 |
|------|----|----|
| Persistence | Many files plus shell globals | Append-only JSONL ledgers plus disposable projections |
| Runtime implementation | Bash sourcing/subprocesses | Elixir supervisors, GenServers, Tasks, Ports |
| Collaboration | Kanban/GitHub Issues/GitHub PRs | JSONL work items and git-native change sets on `indexer/control` |
| Agent deterministic code | Shell script override | Deterministic hook: Elixir module or executable command |
| Git side effects | Often embedded in workflow agents | Declared effect outbox entries; workspace writes allowed only in work branch |
| Hosted forge | GitHub-aware core | Git-only core; hosted forges are optional adapters |

## Directory Structure

The exact implementation layout may vary, but the logical structure is:

```text
indexer/
├── bin/
│   └── indexer                 # CLI entry point
├── lib/
│   ├── indexer/                # OTP application
│   │   ├── agents/             # Agent definitions and renderer
│   │   ├── runtime/            # Runtime adapter behaviours and implementations
│   │   ├── pipeline/           # Pipeline loader, validator, engine
│   │   ├── services/           # Service scheduler and service modules
│   │   ├── workers/            # Worker lifecycle, registry, worktree manager
│   │   ├── scheduler/          # Work queue, priority calculation, conflict checks
│   │   ├── git/                # Git operations and change-set model
│   │   ├── state/              # JSONL append, replay, projection
│   │   ├── effects/            # Durable effect outbox and effect executors
│   │   └── control_branch/     # Self-hosted forge records
│   └── indexer_web/            # Optional web/API endpoint
├── config/
│   ├── agents/                 # Built-in agent definitions
│   ├── pipelines/              # Built-in pipeline definitions
│   ├── services/               # Service definitions
│   └── schemas/                # JSON/YAML schemas
├── formal/                     # TLA+ models carried forward and updated
└── test/
```

Runtime project state lives under `.indexer/` in the target repository:

```text
.indexer/
├── state/
│   ├── work_items.jsonl
│   ├── dependencies.jsonl
│   ├── workers.jsonl
│   ├── pipeline_runs.jsonl
│   ├── pipeline_node_runs.jsonl
│   ├── agent_runs.jsonl
│   ├── agent_events.jsonl
│   ├── contexts.jsonl
│   ├── artifacts.jsonl
│   ├── change_sets.jsonl
│   ├── reviews.jsonl
│   ├── review_comments.jsonl
│   ├── effects.jsonl
│   ├── services.jsonl
│   ├── control_sync.jsonl
│   └── projections/
├── worktrees/
│   └── worker-<work-id>-<attempt>/
├── services/
├── sockets/
├── logs/
└── tmp/
```

Projection files are caches. They must be rebuildable from JSONL.

## Component Overview

### CLI and Web/API Control Plane

The control plane provides:

- work item creation and edits,
- worker start/stop/resume/fix/merge commands,
- service status and manual service runs,
- pipeline/agent inspection,
- event/log streaming,
- review comment and change-set views.

CLI and web/API must read from the same JSONL-backed projections and append the
same state events. There must not be separate CLI-only state.

### Service Scheduler

The service scheduler remains a first-class orchestration model. In Elixir, services
are supervised processes or scheduled jobs rather than bash functions, but the v1
schema concepts stay:

- phases: `startup`, `pre`, `periodic`, `post`, `shutdown`,
- schedule types: `tick`, `interval`, `cron`, `event`, `continuous`,
- execution types: `function`, `command`, `pipeline`, `agent`,
- conditions, groups, dependencies, concurrency, restart policy, circuit breaker,
  health checks, limits, metrics.

Tick-phase services run synchronously in scheduler order. Periodic/event/continuous
services are supervised asynchronous jobs.

### Scheduler

The scheduler builds a unified work queue from JSONL work items and change-set
events. It preserves the v1 priority model:

- base priority,
- plan bonus,
- aging bonus,
- dependency/dependent bonus,
- sibling work-in-progress penalty,
- resume bonus,
- resume fail penalty,
- skip cooldown with exponential backoff,
- dependency cycle exclusion,
- file conflict prevention.

Scheduler output is not direct process mutation. It appends scheduling decisions
and starts workers through the worker supervisor.

### Workers

Each worker has:

- a work item,
- an isolated git worktree,
- a work branch,
- a pipeline run,
- a lifecycle state,
- a lease,
- append-only event records.

Workers are isolated at the git/workspace boundary. They may share project-level
read-only context and control-branch records, but writable code changes stay in
their worktree and work branch.

### Pipeline Engine

The pipeline engine is the v1 jump-based state machine implemented in Elixir.

It preserves:

- ordered step list,
- result mapping resolution,
- inline handlers,
- named jumps,
- max visits,
- on-max routing,
- enabled-by skipping,
- readonly checkpoint/restore,
- commit-after behavior,
- unknown-result backup extraction,
- circuit breaker for repeated non-terminal results,
- cost budget checks,
- step timeout handling,
- current-step persistence for resume.

Pipeline state is appended to JSONL and projected into current state.

### Agents

Agents are still modular single-purpose units. The v2 model makes the existing
markdown-plus-shell split explicit:

- **Markdown objective**: nondeterministic model-facing instructions.
- **Deterministic hooks**: Elixir module or external executable that prepares
  context, validates output, extracts result tags, checks completion, commits
  controlled effects, or performs non-model work.

Shell remains allowed as a hook language. It is no longer the only extension
mechanism.

### Runtime Layer

The runtime layer remains backend-agnostic. It hides Codex, Claude, OpenCode, Pi,
and custom runtime differences from agents and pipelines.

The runtime layer owns:

- backend discovery,
- command/session construction,
- app-server/CLI process supervision,
- retry and rate-limit logic,
- session resume semantics,
- prompt wrapping,
- text/session extraction,
- backend event normalization.

### Git and Change Sets

Indexer replaces GitHub Pull Requests with git-native change sets.

A change set includes:

- work item id,
- worker id,
- target ref,
- base sha,
- work branch,
- head sha,
- affected files,
- validation results,
- review records,
- merge state,
- conflict state.

Change sets are stored in JSONL and mirrored to the `indexer/control` branch.
Merges use normal git operations. Hosted forges may be optional adapters, not core
state.

### Control Branch

The `indexer/control` branch is the self-hosted collaboration surface. It contains
human-reviewable records and snapshots:

```text
work_items/<id>.md
work_items/<id>.json
change_sets/<id>/change_set.json
change_sets/<id>/summary.md
reviews/<id>/review.json
reviews/<id>/comments/<comment-id>.md
runs/<id>/summary.json
runs/<id>/events.jsonl
state/*.jsonl
snapshots/*.json
workflows/*.json
agents/*.md
```

The local JSONL ledgers drive scheduling. The control branch is the portable
history, sync surface, and review surface.

## Persistent State

### JSONL Record Envelope

All ledgers use one newline-terminated JSON object per event:

```json
{
  "id": "evt_01HZY...",
  "stream": "pipeline_runs",
  "aggregate_id": "run_01HZY...",
  "type": "pipeline.step.completed",
  "schema_version": 1,
  "timestamp": "2026-05-07T12:00:00Z",
  "actor": {"type": "service", "id": "pipeline-supervisor"},
  "causation_id": "evt_...",
  "correlation_id": "work_...",
  "payload": {}
}
```

Requirements:

- Append-only.
- Atomic single-record append under per-ledger lock.
- Every record has stable id and timestamp.
- Every state transition has an aggregate id.
- No in-place edits.
- Recovery truncates a ledger to the last complete newline if needed.
- Projections are deterministic folds over ledgers.

### Core Ledgers

| Ledger | Purpose |
|--------|---------|
| `work_items.jsonl` | Work item lifecycle, title/body/status/priority/target ref changes |
| `dependencies.jsonl` | Dependency graph and satisfaction state |
| `workers.jsonl` | Worker leases, process state, workspace, lifecycle events |
| `pipeline_runs.jsonl` | Pipeline run lifecycle and current step |
| `pipeline_node_runs.jsonl` | Step visits, outcomes, routing decisions |
| `agent_runs.jsonl` | Agent invocation lifecycle and extracted result |
| `agent_events.jsonl` | Raw/normalized runtime stream events |
| `contexts.jsonl` | Rendered prompts, context sections, summaries |
| `artifacts.jsonl` | Artifact metadata, digests, storage refs |
| `change_sets.jsonl` | Work branch and merge state |
| `reviews.jsonl` | Review decisions and summaries |
| `review_comments.jsonl` | Inline/general comments and resolution |
| `effects.jsonl` | Pending/completed/failed side effects |
| `services.jsonl` | Service state, metrics, circuit breakers, queues |
| `control_sync.jsonl` | Control branch import/export records |

### Disposable Projections

Indexer may maintain:

```text
.indexer/state/projections/work_items.current.json
.indexer/state/projections/workers.current.json
.indexer/state/projections/services.current.json
.indexer/state/projections/queue.current.json
```

Projection corruption is not fatal. Delete and replay ledgers.

## Worker Lifecycle

The worker lifecycle is carried forward from `config/worker-lifecycle.json` and
`formal/WorkerLifecycle.tla`, with GitHub-specific effect names generalized.

States:

| State | Type | Meaning |
|-------|------|---------|
| `none` | initial | No active worker state |
| `needs_fix` | waiting | Change set needs agent fix/review-comment handling |
| `fixing` | running | Fix worker active |
| `fix_completed` | transient | Fix completed, immediately advances |
| `needs_merge` | waiting | Change set ready for merge attempt |
| `merging` | running | Merge worker active |
| `merge_conflict` | waiting | Merge conflict detected |
| `needs_resolve` | waiting | Single change-set conflict resolution needed |
| `needs_multi_resolve` | waiting | Multi-change-set conflict resolution needed |
| `resolving` | running | Conflict resolver active |
| `resolved` | transient | Resolution completed, immediately advances |
| `merged` | terminal | Change set landed |
| `failed` | terminal_recoverable | Manual or scheduled recovery may resume |

Core event families:

- `worker.spawned`
- `fix.detected`, `fix.started`, `fix.pass`, `fix.partial`, `fix.skip`,
  `fix.fail`, `fix.timeout`, `fix.already_merged`
- `merge.start`, `merge.succeeded`, `merge.already_merged`, `merge.conflict`,
  `merge.out_of_date`, `merge.transient_fail`, `merge.hard_fail`
- `conflict.needs_resolve`, `conflict.needs_multi`
- `resolve.started`, `resolve.succeeded`, `resolve.fail`, `resolve.timeout`,
  `resolve.stuck_reset`, `resolve.already_merged`
- `review.comments_detected`
- `recovery.to_fix`, `recovery.to_resolve`
- `startup.reset`
- `change_set.merged`
- `resume.abort`, `resume.retry`
- `task.reclaim`
- `task.pending_review`
- `manual.start_merge`, `manual.start_fix`
- `worker.completion`, `worker.failure`
- `user.full_reset`, `user.reset_to_fix`, `user.reset_to_resolve`

The v1 `kanban` marker is replaced by `work_item.status` and `change_set.status`
events, but the state categories remain:

| V1 Marker | V2 Status |
|-----------|-----------|
| `[ ]` | `pending` |
| `[=]` | `in_progress` |
| `[P]` | `pending_review` |
| `[x]` | `merged` |
| `[*]` | `failed` |
| `[N]` | `not_planned` |

Dependencies are satisfied only by `merged`, not by `pending_review`.

## Effect Outbox

The outbox pattern is mandatory. Lifecycle transitions record desired effects before
executing them.

Effect record shape:

```json
{
  "id": "eff_01H...",
  "batch_id": "batch_01H...",
  "scope_type": "worker",
  "scope_id": "worker-WI-001-1",
  "effect_type": "git.merge_change_set",
  "idempotency_key": "git.merge_change_set:cs_123:head_sha",
  "status": "pending",
  "attempts": 0,
  "payload": {}
}
```

Execution order follows the TLA model:

1. Append state transition event.
2. Append any work item/change-set status event.
3. Append pending effect records.
4. Execute each effect idempotently.
5. Append effect completion or failure event.

Cleanup effects must run after all other pending effects for the same scope have
been applied or safely skipped.

## Data Flow

1. Work item is created via CLI, web/API, control branch import, or optional
   external tracker adapter.
2. Scheduler projects ledgers and selects eligible work.
3. Worker supervisor creates worktree and work branch.
4. Pipeline engine starts a pipeline run and writes current-step records.
5. Agent step renders objective/context and invokes runtime adapter.
6. Runtime adapter writes raw and normalized events to JSONL.
7. Agent extraction hook writes gate result and artifacts.
8. Pipeline routes using result mappings.
9. Deterministic hooks and configured effect executors request outbox effects.
10. Git effect executors create commits, change sets, reviews, merges, and control
    branch records.
11. Service scheduler keeps polling/reconciling until terminal state.

## Design Rules

- Preserve v1 contracts unless a v2 deviation is named in this spec.
- Agent output is nondeterministic; state transitions are deterministic.
- Every durable decision is append-only JSONL.
- Every side effect is replayable or has an idempotency key.
- GitHub is optional integration, never core state.
- The git control branch is the portable collaboration layer.
- Pipeline schema compatibility matters more than abstract workflow novelty.
