# Indexer Architecture Specification

Status: Draft v2
Target implementation: Elixir/OTP
Compatibility target: new product architecture; no `.ralph` or v1 shell compatibility requirement

## Purpose

Indexer is a long-running agent orchestration system. It turns repository-owned work
items into isolated agent workspaces, runs external coding agents against those
workspaces, records their behavior, and lands acceptable changes using git.

Indexer is not an agent harness. It does not implement model reasoning, tool use, or
interactive coding behavior. It prepares context, launches external agent runtimes,
normalizes their events, runs deterministic hooks, and advances durable workflow state.

The design is influenced by the Symphony pattern: decouple work from individual agent
sessions, let work items drive orchestration, and treat pull requests/sessions as
implementation details rather than the core domain. Indexer differs by making git
itself the collaboration substrate instead of depending on GitHub, Linear, or any
hosted tracker.

## Goals

- Implement orchestration in Elixir/OTP with supervised services, process isolation,
  restart recovery, and observable runtime state.
- Use SQLite as the authoritative local runtime database.
- Use a git control branch as the portable collaboration and audit surface.
- Support external agents through adapter contracts for Codex, Claude Code, OpenCode,
  Pi, and future runtimes.
- Model agents as a nondeterministic objective plus deterministic hooks.
- Model workflows as flexible pipelines that can express implementation, research,
  validation, review, maintenance, and meta-work without baking in GitHub-specific
  states.
- Keep all important history visible in the repository through commits, work branches,
  control-branch records, and merge commits.

## Non-Goals

- GitHub Issues, GitHub Pull Requests, GitHub Actions, or GitHub-specific review APIs
  are not core dependencies.
- The system does not preserve v1 `.ralph` file layouts, shell APIs, or JSON schemas.
- The system is not a general-purpose distributed job scheduler.
- The system does not prescribe one sandbox or approval posture for every agent.
- The system does not assume every workflow produces code; analysis-only and planning
  work are first-class.

## System Overview

Indexer has five core layers:

1. **Control Plane**
   - CLI and web/API surfaces.
   - Work item creation, status changes, review comments, operator actions.
   - Reads and writes SQLite.
   - Syncs user-visible records to the git control branch.

2. **Coordination Layer**
   - OTP supervisors, service daemon, schedulers, worker registry, leases.
   - Decides which work items are eligible, which workers to run, and which effects
     need replay.
   - Owns retries, backoff, cancellation, and reconciliation.

3. **Workflow Layer**
   - Pipeline engine, node graph validation, dataflow, branch routing, gates.
   - Executes agent objectives and deterministic hooks.
   - Produces normalized outcomes and requested effects.

4. **Execution Layer**
   - Runtime adapters for external agent harnesses.
   - Workspace manager, process supervision, stream normalization, approvals,
     timeout handling, session persistence.

5. **Repository Layer**
   - Git workspaces, work branches, merge operations, and the control branch.
   - No hosted forge is required.

## Persistent State

SQLite is the authoritative runtime store. All orchestration decisions must be
recoverable from SQLite plus git.

Minimum tables:

- `work_items`: id, title, body, kind, status, priority, parent_id, target_ref,
  created_by, timestamps.
- `dependencies`: blocked_id, blocker_id, relation, status.
- `workers`: id, work_item_id, workspace_path, branch_name, pid, status,
  current_pipeline_run_id, lease_owner, timestamps.
- `pipeline_runs`: id, workflow_id, work_item_id, worker_id, status, started_at,
  completed_at, current_node_id.
- `pipeline_node_runs`: id, pipeline_run_id, node_id, node_type, status, outcome,
  visit_count, input_context_id, output_context_id, timestamps.
- `agent_runs`: id, node_run_id, agent_id, runtime_adapter, runtime_session_id,
  status, objective_digest, started_at, completed_at, exit_code.
- `agent_events`: id, agent_run_id, sequence, event_type, normalized_payload,
  raw_payload, timestamp.
- `contexts`: id, scope, content_markdown, content_json, digest, created_at.
- `artifacts`: id, owner_type, owner_id, kind, storage_uri, digest, metadata.
- `change_sets`: id, work_item_id, worker_id, branch_name, base_ref, head_sha,
  status, merge_strategy, metadata.
- `reviews`: id, change_set_id, status, summary, decision, metadata.
- `review_comments`: id, review_id, file_path, line, body, status, author_type.
- `effects`: id, scope_type, scope_id, effect_type, payload, idempotency_key,
  status, attempts, last_error, timestamps.
- `services`: id, status, lease_owner, last_run_at, next_run_at, failure_count,
  circuit_state.
- `control_sync`: id, direction, control_ref, local_commit, status, last_error.

SQLite stores raw and normalized logs. Files are optional artifacts, not the primary
communication channel between Indexer and agents.

## Git Control Branch

Indexer uses a repository branch named `indexer/control` as its self-hosted forge.
This branch is an orphan-style metadata branch and does not need to share the main
source tree.

The control branch is the durable collaboration record:

```text
tasks/<work-item-id>.json
tasks/<work-item-id>.md
reviews/<review-id>/review.json
reviews/<review-id>/summary.md
reviews/<review-id>/comments/<comment-id>.md
runs/<run-id>/summary.json
runs/<run-id>/events.jsonl
workflows/<workflow-id>.json
snapshots/state.json
```

SQLite remains authoritative for local scheduling. The control branch is the
portable audit log and synchronization medium between machines. Sync is performed
by deterministic effects, not by nondeterministic agent turns.

## Git-Native Change Model

Indexer replaces pull requests with repository-native change sets.

- A work item runs in an isolated git worktree.
- A worker writes commits to a work branch such as
  `indexer/work/<work-item-id>/<attempt>`.
- A change set records base ref, head sha, author metadata, generated summary,
  validation results, and review comments.
- Review comments live in SQLite and are mirrored to `indexer/control`.
- Merge workers use git operations directly: fast-forward, merge commit, rebase,
  cherry-pick, or configured custom strategy.
- Merge results are committed to the target branch and recorded in the control branch.

Hosted forges may be adapters later, but the core product must work with any git
remote.

## Runtime Directory

Indexer may use a local runtime directory named `.indexer/` for SQLite, sockets,
temporary files, and worktrees:

```text
.indexer/
  indexer.sqlite3
  logs/
  sockets/
  worktrees/
  temp/
```

This directory is implementation-local and is not a compatibility contract. Durable
project history belongs in normal git branches and `indexer/control`.

## OTP Process Topology

Recommended top-level supervision tree:

- `Indexer.Application`
  - `Indexer.Repo` for SQLite access.
  - `Indexer.EventBus` for PubSub.
  - `Indexer.ControlBranch.Supervisor`.
  - `Indexer.ServiceSupervisor`.
  - `Indexer.WorkerSupervisor`.
  - `Indexer.RuntimeSupervisor`.
  - `Indexer.EffectSupervisor`.
  - `IndexerWeb.Endpoint` when web service is enabled.

Long-running responsibilities must be represented as supervised processes:

- Scheduler.
- Service daemon.
- Worker registry.
- Agent runtime sessions.
- Control branch sync.
- Effect outbox replay.
- Git merge workers.
- Web/API endpoint.

## Data Flow

1. A work item is created through CLI, web/API, control branch sync, or an optional
   external tracker adapter.
2. Scheduler marks eligible work based on status, dependencies, concurrency, leases,
   conflicts, and policy.
3. Worker manager creates or resumes an isolated worktree and work branch.
4. Pipeline engine creates a pipeline run and executes nodes.
5. Agent nodes render objective/context records and invoke an external runtime adapter.
6. Runtime adapter streams raw backend logs into SQLite and emits normalized events.
7. Deterministic hooks validate, parse, transform, or apply effects.
8. Pipeline emits requested effects, including git commit/merge/control-branch writes.
9. Effect outbox executes idempotent effects and records completion.
10. Control branch sync publishes durable summaries and collaboration records.

## Design Rules

- Nondeterministic model output must not directly mutate orchestration state.
- Agent backends are responsible for their own log formats; adapters normalize them.
- Pipelines express workflow intent, not concrete GitHub or shell assumptions.
- Side effects are declared, durable, replayable, and idempotent.
- Git is a first-class platform boundary; GitHub is optional.
- The control branch is the product’s built-in collaboration surface.
