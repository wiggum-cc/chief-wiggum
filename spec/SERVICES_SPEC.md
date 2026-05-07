# Services Specification

Status: Draft v2
Target implementation: Elixir/OTP

## Purpose

Indexer services are supervised runtime processes that keep orchestration moving.
The v1 service daemon concept was correct; Elixir should implement it directly with
OTP supervisors, GenServers, Tasks, timers, and PubSub instead of shell service
runners.

Services are not pipeline nodes. Services operate the system. Pipelines operate work
items.

## Service Model

Each service has:

- `id`
- `kind`
- `enabled`
- `schedule`
- `concurrency`
- `dependencies`
- `restart_policy`
- `circuit_breaker`
- `lease`
- `telemetry`

Canonical shape:

```yaml
id: scheduler
kind: singleton
module: Indexer.Services.Scheduler
enabled: true
schedule:
  type: interval
  every_ms: 5000
restart_policy:
  strategy: permanent
  max_restarts: 10
  max_seconds: 60
concurrency:
  max_instances: 1
circuit_breaker:
  enabled: true
  failure_threshold: 5
  cooldown_ms: 300000
```

## Service Kinds

### `singleton`

A long-running GenServer. Exactly one instance per Indexer node.

Examples:

- scheduler,
- worker registry,
- control branch sync,
- event compactor,
- web presence tracker.

### `periodic`

A supervised job triggered on interval or cron-like schedule.

Examples:

- retry stale effects,
- publish control branch snapshot,
- prune old log blobs,
- reconcile git branches.

### `pool`

A supervised worker pool with bounded concurrency.

Examples:

- agent runtime pool,
- git merge pool,
- hook execution pool,
- control branch import pool.

### `watcher`

A process that subscribes to OS, git, database, or web events and emits Indexer
events.

Examples:

- file/worktree watcher,
- remote git ref watcher,
- runtime socket watcher.

### `endpoint`

Web/API service. Usually Phoenix endpoint or Plug-based HTTP service.

## Core Services

### Scheduler

Selects eligible work items and starts worker pipelines.

Inputs:

- work items,
- dependencies,
- leases,
- worker capacity,
- repository conflict hints,
- service mode.

Outputs:

- worker start requests,
- deferred/retry state,
- scheduling events.

### Worker Registry

Tracks live workers and reconciles database state with OS processes.

Responsibilities:

- maintain leases,
- detect dead processes,
- resume or mark interrupted workers,
- route cancellation,
- expose status to CLI/web.

### Pipeline Supervisor

Starts and supervises pipeline runs for workers.

Responsibilities:

- validate workflow graph,
- execute nodes,
- persist node state,
- route terminal outcomes,
- emit pipeline events.

### Runtime Supervisor

Owns external agent runtime processes.

Responsibilities:

- start app-server/CLI processes,
- stream logs,
- cancel turns,
- kill process trees,
- restart only when policy allows.

### Effect Outbox

Executes durable side effects.

Responsibilities:

- poll pending effects,
- enforce idempotency,
- retry with backoff,
- mark completion,
- surface permanent failures.

### Git Merge Service

Executes git-native change-set operations.

Responsibilities:

- create work branches,
- rebase,
- merge,
- detect conflicts,
- record merge metadata,
- update control branch records.

### Control Branch Sync

Synchronizes SQLite state with `indexer/control`.

Responsibilities:

- import new work items and comments,
- publish local snapshots and records,
- resolve control branch conflicts deterministically,
- commit sync results.

### Web/API Endpoint

Provides status and control surfaces.

Responsibilities:

- task/work item CRUD,
- worker status,
- pipeline run inspection,
- log/event streaming,
- review comments,
- operator actions.

## Scheduling

Supported schedules:

- `always`: run as supervised process.
- `interval`: run every N milliseconds.
- `cron`: optional later extension.
- `event`: run when matching Indexer event appears.
- `manual`: only via CLI/API.

Event schedules match normalized events, not backend-specific raw logs.

## Leases And Multi-Node

SQLite supports single-node operation by default. Multi-node operation is possible
when machines share a database or coordinate through the git control branch, but v2
does not require full distributed consensus.

Every service or worker that mutates state must hold a lease:

- lease owner,
- acquired_at,
- expires_at,
- heartbeat_at.

Expired leases are recoverable by reconciliation services.

## Circuit Breakers

Services and effect types may define circuit breakers:

- failure threshold,
- cooldown,
- half-open attempt count,
- reset on success.

Circuit breaker state is stored in SQLite so restarts do not erase failure history.

## Observability

All services emit telemetry events:

- start,
- stop,
- tick,
- job_started,
- job_completed,
- job_failed,
- circuit_opened,
- circuit_closed,
- lease_acquired,
- lease_lost.

Web and CLI surfaces consume the same event stream.

## Validation Rules

A service config is valid only if:

- `id` is unique.
- module exists.
- schedule is valid.
- dependencies exist.
- pool sizes are positive.
- restart policy is compatible with service kind.
- services that mutate state declare lease behavior.

## Relationship To Pipelines

Services may start pipelines, cancel pipelines, or reconcile pipeline state. Services
must not encode workflow-specific business logic that belongs in a pipeline.

For example:

- The Scheduler may start `default-implementation` for a work item.
- The Pipeline decides whether to implement, validate, review, or merge.
- The Effect Outbox executes the merge effect requested by the pipeline.
