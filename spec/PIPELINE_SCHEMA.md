# Pipeline Schema Specification

Status: Draft v2

## Purpose

Pipelines describe how Indexer moves a work item through objectives, deterministic
steps, gates, reviews, and effects. A pipeline is a workflow graph, not a hardcoded
engineering lifecycle.

The v1 model of ordered steps with result-based jumps was useful, but too much policy
was embedded in fixed agent roles and GitHub PR assumptions. The v2 model keeps the
good parts: bounded state machines, explicit routing, remediation loops, and
declarative configuration. It removes baked-in side effects and lets workflows define
their own node types, outcomes, and gates.

## Top-Level Shape

```yaml
id: default-implementation
version: 2
description: Implement, validate, review, and merge a work item.

inputs:
  - work_item
  - repository

nodes:
  - id: implement
    type: agent
    agent: engineering.implementation
    max_visits: 3
    routes:
      succeeded: validate
      needs_work: implement
      blocked: stop_blocked
      failed: fail

  - id: validate
    type: hook
    hook:
      kind: module
      module: Indexer.Hooks.RunRepositoryValidation
    routes:
      succeeded: review
      needs_work: implement
      failed: fail

  - id: review
    type: agent
    agent: engineering.review
    routes:
      approved: record_change_set
      changes_requested: implement
      failed: fail

  - id: record_change_set
    type: effect
    effect: git.record_change_set
    routes:
      succeeded: merge
      failed: fail

  - id: merge
    type: effect
    effect: git.merge_change_set
    routes:
      succeeded: done
      conflict: resolve_conflict
      failed: fail

terminal:
  succeeded: done
  failed: fail
  blocked: stop_blocked
```

## Node Types

### `agent`

Runs a nondeterministic objective through an external runtime adapter.

Required:

- `agent`

Optional:

- `runtime_overrides`
- `context`
- `max_visits`
- `timeout_seconds`
- `capabilities`
- `routes`

### `hook`

Runs deterministic logic. Hooks may parse output, validate a workspace, generate
context, compute routing data, or request effects.

Required:

- `hook`

Hooks may be pure or side-effecting. Side-effecting hooks must declare idempotency
keys and permissions.

### `gate`

Evaluates an expression against pipeline data and routes without launching an agent
or external command.

```yaml
- id: check_complexity
  type: gate
  when: "work_item.complexity == 'high'"
  routes:
    true: architecture_review
    false: implement
```

### `effect`

Requests or executes a durable side effect through the effect outbox.

Effects include:

- `git.create_work_branch`
- `git.record_change_set`
- `git.merge_change_set`
- `git.rebase_change_set`
- `git.write_control_branch`
- `control.create_work_item`
- `control.add_review_comment`
- `workspace.cleanup`

Pipeline nodes request effects; the effect engine executes them idempotently.

### `subpipeline`

Runs another pipeline with scoped inputs and returns its terminal outcome.

### `wait`

Waits for an external condition or event, such as operator review, CI-like workflow
completion, or another work item completing.

## Routing

Routes map node outcomes to next node ids or terminal statuses.

```yaml
routes:
  succeeded: next_node
  needs_work: implement
  failed: fail
  "*": fail
```

Outcome names are strings. They are not globally hardcoded. Standard outcome names
are recommended:

- `succeeded`
- `approved`
- `changes_requested`
- `needs_work`
- `blocked`
- `conflict`
- `failed`
- `skipped`
- `inconclusive`

If no route matches, the pipeline fails validation unless a wildcard route exists.

## Dataflow

Nodes read immutable inputs from:

- work item fields,
- repository metadata,
- prior node outputs,
- contexts,
- artifacts,
- runtime events,
- effect results.

Nodes write:

- node output JSON,
- context records,
- artifacts,
- requested effects,
- terminal outcome.

No node mutates prior node output.

## Side-Effect Boundary

Side effects must be explicit. Pipelines must not hide git operations inside
agent-specific assumptions.

Allowed side-effect paths:

1. A deterministic hook declares and performs a side effect with an idempotency key.
2. A node requests an effect and the effect engine executes it.
3. An external agent modifies only its assigned workspace/work branch under its
   declared runtime capabilities.

Global project state changes, target branch merges, control branch writes, and
workspace cleanup must go through the effect engine.

## Retry And Bounds

Each node may define:

- `max_visits`
- `retry_policy`
- `timeout_seconds`
- `circuit_breaker`
- `on_max`

```yaml
retry_policy:
  max_attempts: 3
  backoff:
    initial_ms: 10000
    multiplier: 2
    max_ms: 300000
```

Every cycle in the graph must contain at least one bounded node or an explicit wait
for operator/external input. Pipeline validation rejects unbounded automatic cycles.

## Terminal States

Pipelines define their own terminal states. Recommended terminal states:

- `done`
- `failed`
- `blocked`
- `cancelled`
- `abandoned`
- `draft`

Terminal state changes update SQLite and may request control branch publication.

## Validation Rules

A pipeline is valid only if:

- All node ids are unique.
- All route targets exist or refer to declared terminal states.
- All automatic cycles are bounded.
- All agents and hooks resolve.
- Effect types resolve.
- Required capabilities are compatible with agent and pipeline policy.
- Wait nodes name resumable conditions.
- Side-effecting hooks or effects define idempotency keys.

## Example: Research Workflow

```yaml
id: research-only
version: 2
nodes:
  - id: investigate
    type: agent
    agent: general.researcher
    routes:
      succeeded: summarize
      inconclusive: summarize
      failed: fail
  - id: summarize
    type: hook
    hook:
      kind: module
      module: Indexer.Hooks.PublishResearchSummary
    routes:
      succeeded: done
terminal:
  succeeded: done
  failed: fail
```

This workflow produces no code branch and no merge. That must be valid.
