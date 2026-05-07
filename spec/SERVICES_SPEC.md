# Services Specification

Status: Draft v2
Target implementation: Elixir/OTP
Baseline: Chief Wiggum v1 service scheduler specification

## Overview

The v1 service scheduler is a good architectural decision and remains a first-class
part of Indexer. It gives orchestrator responsibilities a declarative, systemd-like
shape: services have phases, schedules, execution types, conditions, dependencies,
concurrency, restart policies, circuit breakers, health checks, limits, metrics,
and run modes.

The rewrite changes the implementation from shell/Python runners to OTP
supervisors, GenServers, Tasks, timers, and PubSub. It does not replace the service
schema with ad hoc processes.

Services operate the system. Pipelines operate work items.

## Architecture

Logical module layout:

```text
lib/indexer/services/
  loader.ex                # Load, merge, validate service config
  scheduler.ex             # Phase runner and due-service calculation
  runner.ex                # Execute services by type
  state.ex                 # JSONL-backed state/projections
  circuit_breaker.ex       # Circuit breaker decisions
  health.ex                # Health checks
  queue.ex                 # Per-service queued executions
  registry.ex              # Live service process registry
  handlers/                # Allowlisted deterministic service handlers
```

Runtime service state is append-only JSONL:

```text
.indexer/state/services.jsonl
.indexer/state/effects.jsonl
.indexer/state/workers.jsonl
.indexer/state/control_sync.jsonl
.indexer/state/projections/services.current.json
```

Projections are caches and must be rebuildable from JSONL.

## Configuration Schema

Service configuration keeps the v1 root structure:

```json
{
  "version": "2.0",
  "defaults": {},
  "groups": {},
  "services": []
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `version` | string | yes | Service schema version. |
| `defaults` | object | no | Defaults applied to all services. |
| `groups` | object | no | Named groups for bulk enable/disable. |
| `services` | array | yes | Service definitions. |

Schema version `2.0` is retained because the v1 service v2 schema already has the
right concepts. Indexer may introduce `2.x` revisions, but should not discard this
shape without a migration reason.

### Defaults

```json
{
  "defaults": {
    "timeout": 300,
    "restart_policy": {
      "on_failure": "skip",
      "max_retries": 2,
      "backoff": {
        "initial": 5,
        "multiplier": 2,
        "max": 300
      }
    },
    "circuit_breaker": {
      "enabled": false,
      "threshold": 5,
      "cooldown": 300,
      "half_open_requests": 1
    }
  }
}
```

Defaults are merged into service definitions before validation. The effective
config for each run is recorded with service start events.

## Service Definition

Each service requires `id`, `execution`, and either `schedule` or `triggers`.

### Required Fields

| Field | Type | Description |
|-------|------|-------------|
| `id` | string | Unique identifier, pattern `^[a-z][a-z0-9_-]*$`. |
| `schedule` | object | When to run. Required unless `triggers` is set. |
| `triggers` | object | Completion hooks from other services. Alternative to `schedule`. |
| `execution` | object | How to run. |

### Optional Fields

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `description` | string | none | Human-readable description. |
| `enabled` | boolean | `true` | Whether service is enabled. |
| `phase` | string | `periodic` | `startup`, `pre`, `periodic`, `post`, or `shutdown`. |
| `order` | integer | `50` | Execution order within phase. Lower runs first. |
| `required` | boolean | `false` | Abort startup/shutdown when a required service fails. |
| `groups` | array | `[]` | Groups this service belongs to. |
| `depends_on` | array | `[]` | Services that must complete first in the relevant phase/tick. |
| `condition` | object | none | Conditions for execution. |
| `concurrency` | object | default singleton | Concurrency control. |
| `timeout` | integer | default timeout | Execution timeout in seconds. |
| `restart_policy` | object | default policy | Failure handling. |
| `circuit_breaker` | object | default breaker | Circuit breaker config. |
| `health` | object | none | Health checks. |
| `limits` | object | none | Resource limits. |
| `metrics` | object | enabled | Metrics config. |
| `lease` | object | default lease | Multi-process safety lease. |

## Phases

Services run in five phases:

| Phase | When | Execution Model |
|-------|------|-----------------|
| `startup` | Once before main loop | Sequential by `order`, synchronous. Required failures abort startup. |
| `pre` | Every scheduler tick before periodic dispatch | Sequential by `order`, synchronous. |
| `periodic` | Interval/cron/event/continuous | Asynchronous supervised jobs unless configured sync. |
| `post` | Every scheduler tick after periodic dispatch | Sequential by `order`, synchronous. |
| `shutdown` | Once on exit | Sequential by reverse `order`, synchronous. |

Tick-phase services should remain lightweight and deterministic. Long-running work
belongs in periodic/event services, worker pools, or pipelines.

## Schedule Types

### Interval

```json
{
  "type": "interval",
  "interval": 60,
  "jitter": 5,
  "run_on_startup": true
}
```

| Field | Required | Default | Description |
|-------|----------|---------|-------------|
| `type` | yes | none | Must be `interval`. |
| `interval` | yes | none | Seconds between executions. |
| `jitter` | no | `0` | Random jitter in seconds. |
| `run_on_startup` | no | `false` | Run immediately after startup. |

### Cron

```json
{
  "type": "cron",
  "cron": "0 */6 * * *",
  "timezone": "UTC",
  "run_on_startup": false
}
```

Cron format remains `minute hour day month weekday`. Timezone defaults to `UTC`.

### Event

```json
{
  "type": "event",
  "trigger": ["service.succeeded:control-branch-sync", "worker.completed"]
}
```

Trigger matching rules:

- exact string matches exactly,
- suffix wildcard `service.completed:*` matches by prefix,
- arrays match if any element matches.

Common events:

- `service.completed:{id}`,
- `service.succeeded:{id}`,
- `service.failed:{id}`,
- `worker.completed`,
- `worker.failed`,
- `pipeline.completed`,
- `effect.failed:{type}`,
- `control_branch.imported`,
- `change_set.ready`.

### Continuous

```json
{
  "type": "continuous",
  "restart_delay": 5
}
```

Runs continuously, restarting after completion according to restart policy.

### Tick

```json
{
  "type": "tick"
}
```

Runs every scheduler tick. Valid only with `pre` or `post` phase.

## Execution Types

### Command

```json
{
  "type": "command",
  "command": ["git", "fetch", "--prune"],
  "working_dir": "{{project_dir}}",
  "env": {}
}
```

Commands should be argv arrays. String commands may be accepted only when the
service explicitly opts into shell evaluation.

| Field | Required | Description |
|-------|----------|-------------|
| `type` | yes | Must be `command`. |
| `command` | yes | Command argv array or explicitly shell-evaluated string. |
| `working_dir` | no | Working directory. |
| `env` | no | Environment overrides. |

### Function

V1 called allowlisted bash functions with `svc_*` names. V2 keeps the allowlist
idea and generalizes the target:

```json
{
  "type": "function",
  "module": "Indexer.Services.Handlers.Orchestrator",
  "function": "spawn_workers",
  "args": []
}
```

Allowed targets:

- Elixir module/function in a configured handler namespace,
- deterministic executable hook registered under a service handler id.

The loader MUST reject arbitrary module/function references outside the allowlist.

### Pipeline

```json
{
  "type": "pipeline",
  "pipeline": "memory-extract",
  "workspace": false,
  "git_worktree": false,
  "pull_before": false,
  "env": {}
}
```

Pipeline config resolution:

1. project `.indexer/pipelines/{name}.json`,
2. control-branch pipeline records,
3. built-in `config/pipelines/{name}.json`.

Workspace modes:

| Mode | Meaning |
|------|---------|
| `workspace: false` | Run against project read context and service artifact dir. |
| `workspace: true, git_worktree: false` | Create isolated service worker dir without git worktree. |
| `workspace: true, git_worktree: true` | Create git worktree and service work branch. |

Pipeline services are the recommended pattern for scheduled AI reasoning because
they preserve declarative agent configuration and result routing.

### Agent

```json
{
  "type": "agent",
  "agent": "engineering.security-audit",
  "worker_dir": null,
  "max_iterations": 5,
  "max_turns": 20,
  "monitor_interval": 30
}
```

Direct agent services are allowed for simple scheduled tasks, but multi-step AI
services should usually use `pipeline` execution.

## Service Completion Events

When an asynchronous service finishes, the scheduler emits:

| Event | Fired When |
|-------|------------|
| `service.completed:{id}` | Always. |
| `service.succeeded:{id}` | Exit/result success. |
| `service.failed:{id}` | Failure. |

Tick/pre/post services do not emit completion events by default, preventing
unbounded event cascades inside a single tick. Event recursion depth is bounded.

## Triggers

`triggers` is a convenience syntax normalized to `schedule.type = event`.

```json
{
  "id": "control-publish",
  "triggers": {
    "on_complete": ["change-set-optimizer"],
    "on_failure": ["effect-outbox"],
    "on_finish": ["worker-cleanup"]
  },
  "execution": {
    "type": "function",
    "module": "Indexer.Services.Handlers.ControlBranch",
    "function": "publish"
  }
}
```

| Field | Normalized Trigger |
|-------|--------------------|
| `on_complete` | `service.succeeded:{id}` |
| `on_failure` | `service.failed:{id}` |
| `on_finish` | `service.completed:{id}` |

`triggers` and `schedule` are mutually exclusive in source config.

## Conditions

Conditions gate execution:

```json
{
  "condition": {
    "file_exists": ".indexer/worktrees/worker-*",
    "env_set": "INDEXER_RUNTIME_BACKEND",
    "env_equals": {
      "INDEXER_RUN_MODE": "default"
    },
    "env_not_equals": {
      "INDEXER_RUN_MODE": "merge-only"
    },
    "command": ["git", "status", "--porcelain"]
  }
}
```

Supported condition fields:

| Field | Meaning |
|-------|---------|
| `file_exists` | Glob must match at least one file. |
| `file_not_exists` | Glob must match no files. |
| `env_set` | Environment variable must be set. |
| `env_equals` | Environment variables must equal values. |
| `env_not_equals` | Environment variables must not equal values. |
| `command` | Command must exit 0. |
| `ledger_has` | Projection query must match. |
| `service_mode` | Run mode must match. |

All specified conditions must pass.

## Concurrency

```json
{
  "concurrency": {
    "max_instances": 1,
    "if_running": "queue",
    "queue_max": 10,
    "priority": "high"
  }
}
```

| Field | Default | Description |
|-------|---------|-------------|
| `max_instances` | `1` | Maximum concurrent instances. |
| `if_running` | `skip` | `skip`, `queue`, or `kill`. |
| `queue_max` | `10` | Maximum queued runs. |
| `priority` | `normal` | `low`, `normal`, `high`, or `critical`. |

Queue operations are appended to `services.jsonl`.

## Restart Policy

```json
{
  "restart_policy": {
    "on_failure": "retry",
    "max_retries": 3,
    "backoff": {
      "initial": 5,
      "multiplier": 2,
      "max": 300
    }
  }
}
```

| Field | Default | Description |
|-------|---------|-------------|
| `on_failure` | `skip` | `retry`, `skip`, or `abort`. |
| `max_retries` | `2` | Maximum retry attempts. |
| `backoff.initial` | `5` | Initial delay in seconds. |
| `backoff.multiplier` | `2` | Backoff multiplier. |
| `backoff.max` | `300` | Maximum delay in seconds. |

Retries are recorded as separate service run attempts linked by correlation id.

## Circuit Breaker

```json
{
  "circuit_breaker": {
    "enabled": true,
    "threshold": 5,
    "cooldown": 300,
    "half_open_requests": 1
  }
}
```

Circuit states:

| State | Meaning |
|-------|---------|
| `closed` | Normal operation. |
| `open` | Service disabled due to repeated failures. |
| `half-open` | Limited trial run after cooldown. |

Circuit breaker state is appended to JSONL. Restarting Indexer must not reset
failure history.

## Health Checks

```json
{
  "health": {
    "type": "heartbeat",
    "path": ".indexer/services/heartbeat",
    "max_age": 60,
    "interval": 30,
    "on_unhealthy": "restart"
  }
}
```

Health check types:

| Type | Meaning |
|------|---------|
| `file` | File must exist and be fresh. |
| `command` | Command exits 0. |
| `heartbeat` | Service heartbeat event must be fresh. |
| `projection` | Projection query must satisfy predicate. |

`on_unhealthy`: `log`, `restart`, `kill`, or `fail_service`.

## Resource Limits

```json
{
  "limits": {
    "memory": "512M",
    "cpu": 50,
    "nice": 10,
    "timeout_kill": true
  }
}
```

Limits apply to external commands, hooks, agent runtime processes, and supervised
jobs where the host supports enforcement.

## Metrics

```json
{
  "metrics": {
    "enabled": true,
    "emit_to": "both",
    "include_output": false
  }
}
```

Metrics include:

- run count,
- success/failure count,
- duration min/max/total,
- queue length,
- circuit state,
- last run timestamp,
- last failure class.

Metrics are derived from `services.jsonl` and may be exported for dashboards.

## Groups

Groups are preserved:

```json
{
  "groups": {
    "control": {
      "description": "Control branch sync services",
      "enabled": true
    },
    "cleanup": {
      "description": "Cleanup services",
      "enabled": true
    }
  }
}
```

Services list their groups:

```json
{
  "id": "control-branch-sync",
  "groups": ["control", "sync"]
}
```

CLI/API must support enabling and disabling groups.

## Dependencies

```json
{
  "id": "task-spawner",
  "depends_on": ["scheduler-tick", "worker-cleanup"]
}
```

A service runs only after dependencies have completed successfully in the relevant
phase or tick window. Dependency cycles are validation errors.

## State Management

V1 persisted service state to `.ralph/services/state.json`. Indexer appends state
events to `services.jsonl`.

Example records:

```json
{
  "type": "service.started",
  "aggregate_id": "service:control-branch-sync",
  "payload": {
    "run_id": "service_run_123",
    "pid": 12345,
    "started_at": "2026-05-07T12:00:00Z",
    "effective_config": {}
  }
}
```

```json
{
  "type": "service.completed",
  "aggregate_id": "service:control-branch-sync",
  "payload": {
    "run_id": "service_run_123",
    "duration_ms": 481,
    "status": "success",
    "exit_code": 0,
    "metrics": {}
  }
}
```

Tracked projection fields per service:

| Field | Description |
|-------|-------------|
| `last_run` | Last execution timestamp. |
| `status` | `stopped`, `running`, `failed`, `skipped`, `queued`. |
| `run_count` | Total successful runs. |
| `fail_count` | Total failed runs. |
| `consecutive_failures` | Failures since last success. |
| `circuit_state` | Circuit breaker state. |
| `queue` | Pending queued executions. |
| `metrics` | Derived execution metrics. |

## Project Overrides

Projects can override or add services via `.indexer/services.json` and control
branch config.

```json
{
  "version": "2.0",
  "services": [
    {
      "id": "control-branch-sync",
      "schedule": {
        "type": "interval",
        "interval": 120
      }
    },
    {
      "id": "custom-lint-index",
      "enabled": true,
      "phase": "periodic",
      "schedule": {
        "type": "interval",
        "interval": 300
      },
      "execution": {
        "type": "command",
        "command": ["./scripts/rebuild-lint-index"]
      }
    }
  ]
}
```

Override rules:

- existing service fields merge recursively,
- arrays replace unless the field declares append semantics,
- new services are added,
- `"enabled": false` disables a default service.

## Default Services

The default service set should preserve v1 responsibilities while removing the
GitHub dependency from the core.

### Startup Phase

| ID | Order | Description |
|----|-------|-------------|
| `validate-control` | 10 | Validate work item and control-branch records. |
| `init-scheduler` | 20 | Initialize scheduler projections and detect dependency cycles. |
| `preflight-git` | 30 | Validate git repository and configured target ref. |
| `preflight-runtime` | 40 | Validate selected runtime adapters. |
| `restore-workers` | 50 | Reconcile workers from JSONL and worktrees. |
| `restore-effects` | 60 | Replay pending effects when safe. |
| `init-terminal` | 80 | Initialize optional terminal/status UI. |

### Pre Phase

| ID | Order | Description |
|----|-------|-------------|
| `lease-reap` | 10 | Reclaim expired service and worker leases. |
| `resume-poll` | 20 | Check pending runtime/process resumes. |
| `worker-cleanup` | 30 | Reap completed worker processes and append state. |

### Periodic Phase

| ID | Interval | Description |
|----|----------|-------------|
| `control-branch-sync` | 60s | Import/export work items, comments, config, and snapshots. |
| `effect-outbox` | 10s | Execute pending effects with retry. |
| `usage-tracker` | 180s | Update runtime usage and rate-limit state. |
| `change-set-optimizer` | 300s | Optimize git-native merge order for ready change sets. |
| `fix-workers` | 60s | Spawn fix workers for review comments or failed gates. |
| `resume-workers` | 300s | Resume interrupted workers. |
| `resolve-workers` | 60s | Spawn conflict resolution workers. |
| `workflow-runner` | 60s | Run configured CI-like pipelines. |
| `projection-compactor` | 600s | Rebuild projections and compact export artifacts. |

### Post Phase

| ID | Order | Description |
|----|-------|-------------|
| `completion-check` | 10 | Detect all-done or blocked terminal state. |
| `rate-limit-guard` | 20 | Pause worker spawning when runtime rate limited. |
| `scheduler-tick` | 30 | Build work queue and scheduling decisions. |
| `task-spawner` | 40 | Start workers from scheduler decisions. |
| `skip-decay` | 50 | Decay skip cooldowns. |
| `orphan-detection` | 60 | Detect orphan worktrees/workers. |
| `aging-update` | 70 | Update ready-since aging records. |
| `status-display` | 80 | Update terminal/web status projection. |
| `state-projection` | 90 | Persist service projections. |

### Shutdown Phase

| ID | Order | Description |
|----|-------|-------------|
| `final-state-projection` | 10 | Write final projections. |
| `terminal-cleanup` | 20 | Cleanup terminal/status UI. |
| `lease-release` | 30 | Release owned leases. |

Hosted forge sync services may be added as optional adapters, but no startup
preflight should require GitHub auth.

## Change-Set Merge Optimizer

The v1 PR merge optimizer is preserved conceptually and generalized to git-native
change sets.

The optimizer phases remain:

1. gather all ready change sets,
2. analyze affected files and conflict graph,
3. compute optimal independent batch,
4. execute merges with re-evaluation after each success,
5. categorize remaining change sets as needs fix, needs resolve, needs multi
   resolve, or waiting.

State is stored in `change_sets.jsonl` and projections, not hosted forge PR state.
The optimizer may still use the Maximum Independent Set strategy from v1 for small
sets and a greedy approximation for large sets.

## Run Modes

Run modes are preserved:

| Mode | Flag | Behavior |
|------|------|----------|
| `default` | none | Full orchestration: spawn, fix, resolve, merge. |
| `fix-only` | `--fix-only` | Fix existing change sets and merge them when ready. |
| `merge-only` | `--merge-only` | Only merge ready change sets and resolve conflicts. |
| `resume-only` | `--resume-only` | Only resume previously interrupted workers. |

Run mode is exposed as `INDEXER_RUN_MODE` and as structured scheduler context.
Services use conditions to opt in or out.

## CLI/API Reference

The CLI names may change, but these operations must exist:

| Operation | Description |
|-----------|-------------|
| `service list` | List configured services. |
| `service status [id]` | Show service status from projections. |
| `service run <id> [--sync]` | Trigger service manually. |
| `service stop <id>` | Stop a running service. |
| `service config [id]` | Show effective config. |
| `service enable <id>` | Enable service override. |
| `service disable <id>` | Disable service override. |
| `service enable-group <group>` | Enable group. |
| `service disable-group <group>` | Disable group. |

CLI and web/API must append the same state records and read the same projections.

## Security Model

The v1 `svc_*` prefix rule becomes an allowlist model:

- service `function` execution may call only registered handler modules/functions,
- command execution defaults to argv arrays without shell evaluation,
- shell evaluation requires explicit opt-in and policy approval,
- services that mutate state must hold a lease,
- services that execute effects must use effect idempotency keys,
- service config from the control branch must be validated before activation.

## Validation Rules

A service config is valid only if:

- `version` is supported,
- service ids are unique,
- service id pattern is valid,
- every service has `execution` and either `schedule` or `triggers`,
- `schedule` and `triggers` are not both present,
- phase and schedule combination is valid,
- dependencies exist and are acyclic,
- execution target resolves and is allowlisted,
- concurrency values are positive,
- restart/backoff values are non-negative,
- circuit breaker config is coherent,
- conditions are well-formed,
- mutating services declare lease behavior,
- pipeline and agent execution targets resolve.

Validation should report all config errors.

## Debugging

Required debugging surfaces:

```text
indexer service status --json
indexer service config --json
indexer service run control-branch-sync --sync
indexer inspect services
indexer inspect service-runs <service-id>
indexer inspect events --stream services
```

Manual inspection should also be possible by reading JSONL:

```text
.indexer/state/services.jsonl
.indexer/state/projections/services.current.json
```

## Design Rule

Do not move workflow-specific business logic into services because it is
convenient. Services should schedule, reconcile, execute effects, and maintain the
system. Pipeline configuration and agents should decide work-item behavior.
