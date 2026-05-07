# Pipeline Schema Specification

Status: Draft v2
Target implementation: Elixir/OTP
Baseline: Chief Wiggum v1 pipeline schema and `formal/PipelineEngine.tla`

## Overview

Indexer pipelines preserve the v1 ordered-step model. A pipeline is an ordered
array of steps that execute sequentially by default and may override control flow
with result-based handlers.

This specification intentionally does not replace the v1 model with a generic
workflow graph. The old model is already a useful bounded state machine:

- steps have stable ids,
- agents produce gate results,
- results map to status, exit code, and default jumps,
- `on_result` may jump or run an inline remediation agent,
- loops are bounded by `max` and `on_max`,
- readonly steps can be checkpointed and restored,
- `commit_after` gives durable recovery points.

The v2 rewrite changes the implementation substrate and side-effect boundary:

- Elixir executes and supervises the state machine.
- Durable state is append-only JSONL ledgers plus rebuildable projections.
- GitHub Pull Requests are not a pipeline primitive.
- Git writes, control-branch writes, and cleanup are requested through an effect
  outbox unless they are limited to the worker worktree.

## Top-Level Shape

The canonical pipeline document keeps the v1 shape:

```json
{
  "name": "<pipeline-name>",
  "description": "<human-readable description>",
  "result_mappings": {
    "<RESULT>": {
      "status": "success|failure|partial|unknown|pending",
      "exit_code": 0,
      "default_jump": "next"
    }
  },
  "config": {},
  "steps": [
    {
      "id": "<unique-step-id>",
      "agent": "<agent-type>"
    }
  ]
}
```

| Field | Required | Description |
|-------|----------|-------------|
| `name` | yes | Stable pipeline name. |
| `description` | no | Human-readable description. |
| `result_mappings` | no | Pipeline-level result mapping overrides. |
| `config` | no | Pipeline-scoped configuration passed to steps and hooks. |
| `steps` | yes | Ordered array of step definitions. |

Pipeline names are resolved from built-in config, project config, control-branch
config, or explicit CLI/API input. Resolution order is defined by the config spec,
not by the pipeline engine.

## Step Schema

```json
{
  "id": "<unique-step-id>",
  "agent": "<agent-type>",
  "max": 3,
  "on_max": "next",
  "on_result": {},
  "readonly": false,
  "enabled_by": "INDEXER_PLAN_MODE",
  "commit_after": false,
  "timeout_seconds": 3600,
  "cost_budget": 0,
  "config": {},
  "hooks": {
    "pre": [],
    "post": []
  }
}
```

| Field | Required | Default | Description |
|-------|----------|---------|-------------|
| `id` | yes | none | Unique step identifier within the pipeline. |
| `agent` | yes | none | Agent type to execute. |
| `max` | no | `0` | Maximum total visits. `0` means unlimited and is discouraged for loop participants. |
| `on_max` | no | `next` | Jump target when `max` would be exceeded. |
| `on_result` | no | `{}` | Per-result handlers. |
| `readonly` | no | `false` | Run with readonly workspace policy and restore tracked changes after the step. |
| `enabled_by` | no | none | Config or environment key that must resolve truthy for the step to run. |
| `commit_after` | no | `false` | Request a git commit/effect after successful execution. |
| `timeout_seconds` | no | agent default | Step-level timeout. Timeout produces `FAIL` unless overridden by policy. |
| `cost_budget` | no | `0` | Optional step budget. `0` means unlimited. |
| `config` | no | `{}` | Agent-specific configuration for this step. |
| `hooks` | no | `{}` | Deterministic pre/post hook names or hook objects. |

The original v1 field names remain normative. New optional fields may be added,
but implementations must continue to understand the ordered-step semantics above.

## Result Handlers

`on_result` maps gate result values to handlers:

```json
{
  "on_result": {
    "FIX": {
      "id": "audit-fix",
      "agent": "engineering.security-fix",
      "max": 2,
      "commit_after": true
    },
    "FAIL": {
      "jump": "abort"
    }
  }
}
```

A handler is either a jump handler or an inline agent handler.

### Jump Handler

```json
{ "jump": "<target>" }
```

### Inline Agent Handler

Inline handlers reuse the step schema subset:

```json
{
  "id": "<handler-step-id>",
  "agent": "<agent-type>",
  "max": 2,
  "on_max": "next",
  "on_result": {},
  "readonly": false,
  "commit_after": true,
  "timeout_seconds": 1800,
  "config": {},
  "hooks": {
    "pre": [],
    "post": []
  }
}
```

After an inline agent completes:

1. If the inline handler has a matching `on_result`, dispatch on the inline
   agent's result.
2. If the inline handler has no matching result handler, control returns to the
   parent step. This preserves the v1 remediation pattern: fix, then re-run the
   gate that requested the fix.
3. Inline handler `max` is counted for the whole pipeline run, not only for a
   single parent visit.

Inline handlers are syntactic sugar. They can be flattened into top-level steps
with explicit jumps, but inline form is preferred when the handler is reachable
only from one parent step.

## Jump Targets

| Target | Meaning |
|--------|---------|
| `self` | Re-run the current step. |
| `prev` | Jump to the previous top-level step, clamped to the first step. |
| `next` | Continue to the next top-level step. |
| `<id>` | Jump to a top-level step with matching id. |
| `abort` | Halt the pipeline with failure. |

Named jump targets must resolve at validation time. Unknown jump targets are
configuration errors.

## Gate Results

Agents produce a semantic `gate_result`. Standard values remain:

| Value | Typical Meaning |
|-------|-----------------|
| `PASS` | Step passed. |
| `FAIL` | Step failed and should normally abort. |
| `FIX` | Fixable issue was found. |
| `SKIP` | Step is not applicable. |
| `UNKNOWN` | No valid result could be extracted. |

Any string may be used if the agent and pipeline declare a mapping for it.
Unknown unmapped strings abort the pipeline.

## Result Mappings

Result mappings define three independent facts:

- `status`: category written to agent and pipeline result records,
- `exit_code`: process-style result code for CLI surfaces,
- `default_jump`: control flow when no `on_result` handler matches.

Default mappings:

```json
{
  "PASS": { "status": "success", "exit_code": 0, "default_jump": "next" },
  "FAIL": { "status": "failure", "exit_code": 10, "default_jump": "abort" },
  "FIX":  { "status": "partial", "exit_code": 0, "default_jump": "prev" },
  "SKIP": { "status": "success", "exit_code": 0, "default_jump": "next" },
  "UNKNOWN": { "status": "unknown", "exit_code": 1, "default_jump": "self" }
}
```

Resolution order:

1. pipeline `result_mappings`,
2. agent-specific `result_mappings`,
3. global default mappings.

The mapping resolution result is persisted with each node run so replay does not
change if configuration is edited later.

## Execution Semantics

The engine performs the following loop:

1. Resolve the current top-level step.
2. If `enabled_by` is present and false, append a skipped node-run record and
   jump `next` without incrementing visits.
3. If the next visit would exceed `max`, resolve `on_max`.
4. Append a step-started record.
5. Run pre hooks.
6. Invoke the agent through the runtime adapter.
7. Extract a gate result.
8. If result is `UNKNOWN`, attempt backup result extraction when a resumable
   runtime session exists.
9. Apply the circuit breaker for repeated non-terminal results.
10. If `commit_after` is true, request or perform the configured commit effect.
    A commit failure may override an effective `PASS` to `FIX`.
11. Run post hooks.
12. Dispatch using `on_result`, result mapping `default_jump`, or terminal rules.
13. Append routing and current-step records.

Reaching past the last step completes the pipeline successfully. Jumping to
`abort`, exhausting policy budgets, hitting an unrecoverable timeout, or producing
an unmapped result fails the pipeline.

## Max Visits And On-Max Cascades

`max` bounds total visits across the pipeline run:

```json
{ "id": "audit", "agent": "engineering.security-audit", "max": 3 }
```

When control would transfer to a step whose visit count is already at `max`, the
step body is not run. The engine resolves `on_max` instead.

An `on_max` target may itself point to a step that has reached `max`. The engine
tracks the current on-max cascade. If the cascade visits the same step twice, the
pipeline aborts to prevent an infinite on-max loop.

Termination is guaranteed only when every automatic cycle contains at least one
finite `max` whose `on_max` exits the cycle or aborts.

## Backup Result Extraction

When result extraction yields `UNKNOWN`, the engine should attempt a targeted
backup extraction if the runtime adapter provides a session id. The backup turn
asks the external harness to emit only one allowed result value. If recovery
succeeds, the recovered value replaces `UNKNOWN` and is recorded with provenance.

If backup extraction fails, `UNKNOWN` remains and routes through result mappings.
By default `UNKNOWN` jumps to `self`, but the circuit breaker escalates repeated
`UNKNOWN` results to `FAIL`.

## Circuit Breaker

The circuit breaker tracks repeated non-terminal results per step. `FIX` and
`UNKNOWN` are non-terminal by default. `PASS`, `FAIL`, and `SKIP` reset the
counter.

When a step returns the same non-terminal result `N` consecutive times, where `N`
is the configured threshold, the engine records `pipeline.circuit_tripped` and
routes as `FAIL`.

## Readonly Steps

For `readonly: true`:

- the runtime adapter must be launched with readonly policy,
- deterministic hooks must not write to the workspace unless explicitly declared
  as artifact-only hooks,
- Indexer must restore tracked workspace changes after the step,
- reports, summaries, logs, and JSONL state may still be appended.

Readonly is a workspace guarantee. It does not prevent ledgers or artifacts from
being written.

## Commit-After

`commit_after: true` preserves the useful v1 recovery point behavior but changes
the side-effect boundary.

The step may only commit changes in its worker worktree and work branch. The
commit operation must be represented as an idempotent effect, for example:

```json
{
  "effect_type": "git.commit_workspace",
  "scope_id": "node_run_123",
  "idempotency_key": "git.commit_workspace:node_run_123:workspace_sha"
}
```

The commit message is generated deterministically from the work item, step id,
agent id, and extracted summary unless the pipeline provides an explicit template.

No hosted forge action is implied by `commit_after`.

## Hooks

Steps can define deterministic pre and post hooks:

```json
{
  "id": "test",
  "agent": "engineering.test-coverage",
  "hooks": {
    "pre": ["setup_test_env"],
    "post": ["cleanup_artifacts", "collect_test_report"]
  }
}
```

Hook entries may be strings resolved by the hook registry or full hook objects:

```json
{
  "kind": "module",
  "module": "Indexer.Hooks.CollectTestReport",
  "on_error": "soft_fail"
}
```

Hooks receive a JSON envelope containing the work item, worker, pipeline run,
current node run, workspace, prior contexts, artifacts, and hook config. External
hooks return JSON on stdout. Elixir hooks return the same logical envelope.

Hook failure behavior is explicit:

| Policy | Meaning |
|--------|---------|
| `ignore` | Record diagnostics and continue. |
| `soft_fail` | Produce a routable hook result. |
| `hard_fail` | Fail the current node. |

The v1 default was to log hook failures and continue. Indexer should preserve
that default for legacy-style `pre`/`post` string hooks unless overridden.

## Step Context

The pipeline engine provides context to agents and hooks. The v1 environment
variables become structured context keys:

| Context Key | V1 Equivalent | Description |
|-------------|---------------|-------------|
| `pipeline.current.step_id` | `WIGGUM_STEP_ID` | Current step id. |
| `pipeline.current.run_id` | `RALPH_RUN_ID` | Current pipeline run id. |
| `pipeline.parent.step_id` | `WIGGUM_PARENT_STEP_ID` | Previous completed step id. |
| `pipeline.parent.run_id` | `WIGGUM_PARENT_RUN_ID` | Previous node run id. |
| `pipeline.parent.session_id` | `WIGGUM_PARENT_SESSION_ID` | Parent runtime session id when available. |
| `pipeline.parent.result` | `WIGGUM_PARENT_RESULT` | Previous gate result. |
| `pipeline.parent.report` | `WIGGUM_PARENT_REPORT` | Artifact id or exported report path. |
| `pipeline.next.step_id` | `WIGGUM_NEXT_STEP_ID` | Next step id when known. |

Adapters may expose compatibility environment variables to external commands, but
the source of truth is structured context stored in JSONL.

## Runtime State

V1 wrote `pipeline-config.json` in the worker directory. Indexer stores equivalent
state in JSONL:

- `pipeline_runs.jsonl`: pipeline started, current step, terminal status,
- `pipeline_node_runs.jsonl`: visits, inline visits, result, routing, timing,
- `contexts.jsonl`: rendered context and prompt fragments,
- `effects.jsonl`: requested side effects,
- `artifacts.jsonl`: reports, summaries, exported files, large logs.

A projection may materialize a `pipeline-config.json`-like inspection document,
but it is a cache and must be rebuildable from ledgers.

Example run event:

```json
{
  "type": "pipeline.node.completed",
  "aggregate_id": "pipeline_run_123",
  "payload": {
    "node_run_id": "node_456",
    "step_id": "audit",
    "agent": "engineering.security-audit",
    "visit": 2,
    "gate_result": "FIX",
    "effective_result": "FIX",
    "status": "partial",
    "exit_code": 0,
    "default_jump": "prev",
    "next_step_id": "audit-fix"
  }
}
```

## Examples

### Default Implementation Pipeline

```json
{
  "name": "default",
  "description": "Plan, implement, summarize, audit, test, document, and validate.",
  "steps": [
    {
      "id": "planning",
      "agent": "product.plan-mode",
      "readonly": true,
      "enabled_by": "INDEXER_PLAN_MODE"
    },
    {
      "id": "execution",
      "agent": "engineering.software-engineer",
      "max": 3,
      "commit_after": true,
      "config": {
        "max_iterations": 20,
        "max_turns": 50,
        "supervisor_interval": 2
      }
    },
    {
      "id": "summary",
      "agent": "general.task-summarizer",
      "readonly": true
    },
    {
      "id": "audit",
      "agent": "engineering.security-audit",
      "max": 3,
      "readonly": true,
      "on_result": {
        "FIX": {
          "id": "audit-fix",
          "agent": "engineering.security-fix",
          "max": 2,
          "commit_after": true
        },
        "FAIL": { "jump": "abort" }
      }
    },
    {
      "id": "test",
      "agent": "engineering.test-coverage",
      "max": 2,
      "commit_after": true,
      "on_result": {
        "FIX": {
          "id": "test-fix",
          "agent": "engineering.generic-fix",
          "max": 2,
          "commit_after": true
        }
      }
    },
    {
      "id": "docs",
      "agent": "general.documentation-writer",
      "commit_after": true
    },
    {
      "id": "validation",
      "agent": "engineering.validation-review",
      "readonly": true,
      "on_result": {
        "FAIL": { "jump": "execution" }
      }
    }
  ]
}
```

### Inline Handler With Its Own Routing

```json
{
  "id": "audit",
  "agent": "engineering.security-audit",
  "max": 3,
  "on_result": {
    "FIX": {
      "id": "audit-fix",
      "agent": "engineering.security-fix",
      "max": 2,
      "on_result": {
        "PASS": { "jump": "self" },
        "FAIL": { "jump": "abort" }
      }
    }
  }
}
```

`PASS -> self` on the inline handler means re-run the parent audit. `FAIL` aborts.
Unhandled inline results return to the parent step by default.

### Router Agent

```json
{
  "id": "triage",
  "agent": "system.triage",
  "on_result": {
    "SECURITY": { "jump": "audit" },
    "QUALITY": { "jump": "review" },
    "TESTS": { "jump": "test" },
    "PASS": { "jump": "next" }
  }
}
```

Agents may act as routers when their result values are declared and mapped.

## Validation Rules

A pipeline is valid only if:

- `name` is present.
- `steps` is non-empty.
- all step ids are unique,
- all inline handler ids are unique within their parent scope,
- all agents resolve,
- all hooks resolve,
- all named jump targets resolve,
- all automatic cycles are bounded or explicitly operator-gated,
- every declared result handler has a declared or inherited result mapping,
- `enabled_by` references a known config/env key or is marked dynamic,
- `commit_after` is compatible with workspace capabilities,
- readonly steps do not request workspace-write hooks,
- `timeout_seconds`, `max`, and budgets are non-negative,
- effect-producing hooks declare idempotency keys.

Validation should report all discovered errors, not fail at the first one.

## Design Notes

The pipeline schema should stay conservative. Workflow flexibility comes from
agent definitions, result mappings, hooks, and pipeline configuration, not from
discarding the ordered-step state machine. A future graph syntax may compile down
to this schema, but this schema remains the execution contract.
