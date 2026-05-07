# Agent Specification

Status: Draft v2
Target implementation: Elixir/OTP

## Purpose

An Indexer agent is a reusable unit of work made from two parts:

1. **Objective layer**: markdown instructions consumed by a model-backed external
   agent runtime. This layer is nondeterministic.
2. **Deterministic hook layer**: executable programs or Elixir modules that perform
   validation, context preparation, parsing, transformation, or declared side effects.
   This layer is deterministic relative to its inputs.

The split is intentional. Model output may improve over time, but it must be treated
as probabilistic. Hooks are how the system creates stable contracts around that
probabilistic work.

## Agent Definition

Agents are data records loaded from repository config, installed packages, or the
control branch. Markdown remains the preferred format for objectives. Deterministic
hooks may be Elixir modules or external executables written in shell, Python, Rust,
or another language.

Canonical shape:

```yaml
id: engineering.implementation
version: 2
description: Implement a work item in an isolated workspace.

objective:
  format: markdown
  system: |
    You are a software engineering agent...
  user: |
    {{context.main}}
    Complete objective {{work_item.id}}.
  continuation: |
    Continue from the previous run summary.

runtime:
  adapter: codex
  mode: app_server
  sandbox: workspace_write
  approval_policy: unless_trusted
  model: null
  effort: null
  timeout_seconds: 10800

hooks:
  prepare:
    kind: module
    module: Indexer.Hooks.BuildEngineeringContext
  extract_result:
    kind: executable
    command: ["python3", "scripts/extract_result.py"]
  validate_output:
    kind: module
    module: Indexer.Hooks.ValidateAgentResult

contracts:
  inputs:
    - work_item
    - workspace
    - repository
  outcomes:
    - succeeded
    - needs_work
    - blocked
    - failed
    - skipped
  artifacts:
    - kind: report
    - kind: change_summary
```

## Objective Layer

The objective layer describes what the external model-backed runtime should do.

Required fields:

- `system`: stable role, behavioral constraints, safety rules.
- `user`: task-specific instructions rendered with context.

Optional fields:

- `continuation`: prompt used when resuming an existing runtime session.
- `review`: prompt used when an agent is asked to review its own or another
  change set.
- `output_schema`: structured output schema if the runtime supports it.
- `skills` or `tools`: runtime-specific capabilities to expose.

Objective templates may reference context keys such as:

- `{{work_item.id}}`
- `{{work_item.title}}`
- `{{work_item.body}}`
- `{{workspace.path}}`
- `{{repository.target_ref}}`
- `{{pipeline.node_id}}`
- `{{context.<name>}}`
- `{{artifacts.<kind>}}`

Template rendering happens inside Indexer before runtime invocation. Rendered
objectives are stored in SQLite as `contexts` and linked to the `agent_run`.

## Deterministic Hooks

Hooks are deterministic boundary programs. They receive JSON on stdin and return
JSON on stdout. They must not rely on ambient shell globals.

Hook input envelope:

```json
{
  "hook": "prepare",
  "agent_id": "engineering.implementation",
  "work_item": {},
  "pipeline_run": {},
  "node_run": {},
  "workspace": {},
  "repository": {},
  "context": {},
  "artifacts": [],
  "config": {}
}
```

Hook output envelope:

```json
{
  "status": "ok",
  "outcome": null,
  "context": {},
  "artifacts": [],
  "effects": [],
  "diagnostics": []
}
```

Hook statuses:

- `ok`: hook completed successfully.
- `soft_fail`: hook failed but the pipeline may route around it.
- `hard_fail`: hook failed and the current node must fail.

Hooks may be:

- `module`: Elixir module implementing the hook behaviour.
- `executable`: external command with JSON stdin/stdout.
- `pipeline`: nested deterministic pipeline.

## Standard Hooks

Agents may define any hook name, but these names have standard meaning:

- `prepare`: construct or enrich context before the model turn.
- `before_turn`: final deterministic check before runtime invocation.
- `after_event`: inspect normalized runtime events as they stream.
- `extract_result`: turn raw/normalized runtime data into an `AgentResult`.
- `validate_output`: verify required artifacts, schemas, or workspace state.
- `summarize`: produce a durable summary for future context.
- `plan_effects`: convert agent output into requested effects.
- `cleanup`: deterministic cleanup after success, failure, or cancellation.

## Agent Result

Every agent run must end with an `AgentResult`.

```json
{
  "outcome": "succeeded",
  "confidence": 0.82,
  "summary": "Implemented the requested endpoint and tests.",
  "artifacts": [
    {"kind": "report", "artifact_id": "art_123"}
  ],
  "effects": [
    {"type": "git.record_change_set", "payload": {}}
  ],
  "follow_up_work": [
    {"title": "Refactor duplicate helper", "body": "..."}
  ],
  "diagnostics": []
}
```

Outcomes are agent-defined but should use the standard taxonomy when possible:

- `succeeded`
- `needs_work`
- `needs_review`
- `blocked`
- `failed`
- `skipped`
- `inconclusive`

Pipelines map outcomes to control flow. No outcome has global hardcoded behavior.

## Agent Capability Model

Agents declare capabilities they need:

- `workspace_read`
- `workspace_write`
- `git_read`
- `git_write_work_branch`
- `git_merge`
- `control_branch_read`
- `control_branch_write`
- `network`
- `shell`
- `browser`
- `secrets`

Capabilities are enforced by runtime adapter configuration, workspace sandboxing,
and deterministic hook permissions. A model objective may request capabilities, but
only the loaded agent definition and pipeline policy can grant them.

## State Ownership

Agents do not own pipeline state, worker state, or service state.

Agents may produce:

- model messages,
- proposed changes,
- artifacts,
- requested effects,
- follow-up work items,
- review comments.

Indexer owns:

- persistence,
- state transitions,
- effect execution,
- branch publication,
- scheduling,
- retries,
- cancellation.

## Validation Rules

An agent definition is valid only if:

- `id` is globally unique.
- Objective templates render without missing required variables.
- Runtime adapter exists.
- Hook commands or modules resolve.
- Declared outcomes are non-empty.
- Required capabilities are explicit.
- Side-effecting hooks declare idempotency behavior.
- Artifact contracts name storage kind and retention policy.

## Migration Note

The v1 hybrid markdown-plus-shell idea remains, but shell is no longer special.
The new abstraction is markdown objective plus deterministic hook executable. Shell
is one possible hook implementation.
