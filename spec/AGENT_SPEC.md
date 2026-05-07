# Agent Specification

Status: Draft v2
Target implementation: Elixir/OTP
Baseline: Chief Wiggum v1 agent spec and agent registry implementation

## Terminology

The keywords "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD",
"SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" are to be interpreted as in
RFC 2119.

## Overview

An Indexer agent is a reusable unit of work with two layers:

1. A markdown objective consumed by an external model-backed runtime.
2. Deterministic hooks that prepare context, validate prerequisites, parse model
   output, write structured results, and request controlled effects.

This is the same design idea as v1's markdown-plus-shell agents. The rewrite keeps
that split because it separates nondeterministic model work from deterministic
system work. The implementation no longer depends on sourced bash functions or
`.ralph` paths, but the agent contract remains recognizable.

Indexer is an agent harness orchestrator. It does not become Codex, Claude,
OpenCode, Pi, Hermes, PlotCode, ClockCode, or any other agent harness. It renders
agent context, invokes an external runtime adapter, normalizes events, and advances
pipeline state.

## Preserved V1 Contracts

The following v1 concepts remain normative:

- Agents have stable dotted type names such as `engineering.security-audit`.
- Markdown definitions are the base format.
- Deterministic executable extensions may override or augment base behavior.
- Orchestrator agents and leaf agents are distinct categories.
- Markdown agents use YAML frontmatter and tagged prompt sections.
- Required frontmatter includes `type`, `description`, `required_paths`,
  `valid_results`, and `mode`.
- Execution modes are `ralph_loop`, `once`, `live`, and `resume`.
- The lifecycle phases are loading, init, prerequisite check, ready, execution,
  output validation, and cleanup.
- Top-level agents and sub-agents have different lifecycle responsibilities.
- Agent results contain a gate result used by pipeline routing.
- Readonly agents must not mutate the workspace.

## Intentional Deviations From V1

| Area | V1 | Indexer v2 |
|------|----|------------|
| State path | `.ralph/...` | `.indexer/...` |
| Result source | epoch-named JSON files | `agent_runs.jsonl` plus artifact exports |
| Logs | backend-specific files | normalized `agent_events.jsonl` plus raw artifacts |
| Shell extension | sourced `.sh` override | deterministic hook module or executable |
| Runtime | Claude-first bash facade | adapter layer for multiple external harnesses |
| Side effects | often inside agent scripts | requested effects with idempotency keys |

No compatibility with v1 file paths or `.ralph` is required. The design concepts
are carried forward, not the exact shell API.

## 1. Agent Classification

### 1.1 Agent Formats

Agents may be provided in these formats:

| Format | Typical Extension | Role | Priority |
|--------|-------------------|------|----------|
| Declarative Markdown | `.md` | Objective, metadata, prompt templates | Base |
| Deterministic Executable | `.sh`, `.py`, any executable | Hook or deterministic-only agent | Extension |
| Elixir Module | `.ex` | Trusted hook or built-in deterministic agent | Extension |

When markdown and deterministic extensions exist for the same agent type:

1. The markdown definition is loaded first.
2. Deterministic extensions are loaded second.
3. Extensions may add hooks, replace result extraction, add validation, or define
   a deterministic-only execution path.

The v1 "markdown first, shell second" inheritance model is preserved as a design
rule. The v2 implementation should express it through an agent registry and hook
resolver rather than sourcing shell into the orchestrator process.

### 1.2 Agent Categories

| Category | Characteristics |
|----------|-----------------|
| Orchestrator | Coordinates sub-agents or pipeline-local policy. MUST use the runtime and agent registry APIs; MUST NOT call a concrete backend directly. |
| Leaf | Performs one focused task. Invoked by a pipeline step or by an orchestrator agent. |
| Deterministic | Performs only deterministic work, such as git conflict checks or result extraction. MAY skip model runtime invocation. |

Orchestrator agents should be rare. Most workflow structure belongs in pipeline
configuration and deterministic hooks.

## 2. Declarative Markdown Agent Specification

### 2.1 File Structure

A markdown agent file MUST contain:

1. YAML frontmatter delimited by `---`.
2. At least one system prompt section.
3. At least one user prompt section.

Canonical v2 prompt tags:

```markdown
---
type: engineering.security-audit
description: Review the current workspace for security issues.
required_paths: [workspace]
valid_results: [PASS, FIX, FAIL]
mode: ralph_loop
readonly: true
---

<INDEXER_SYSTEM_PROMPT>
...
</INDEXER_SYSTEM_PROMPT>

<INDEXER_USER_PROMPT>
...
</INDEXER_USER_PROMPT>

<INDEXER_CONTINUATION_PROMPT>
...
</INDEXER_CONTINUATION_PROMPT>
```

The v1 tag names map directly to the v2 tags:

| V1 Tag | V2 Tag |
|--------|--------|
| `WIGGUM_SYSTEM_PROMPT` | `INDEXER_SYSTEM_PROMPT` |
| `WIGGUM_USER_PROMPT` | `INDEXER_USER_PROMPT` |
| `WIGGUM_CONTINUATION_PROMPT` | `INDEXER_CONTINUATION_PROMPT` |

The implementation does not need to accept v1 tag names unless a migration tool
chooses to support them.

### 2.2 Frontmatter Schema

#### Required Fields

| Field | Type | Constraints | Description |
|-------|------|-------------|-------------|
| `type` | string | pattern `[a-z]+[a-z0-9-]*(\.[a-z0-9-]+)+` | Agent type identifier. |
| `description` | string | non-empty | Human-readable description. |
| `required_paths` | array | non-empty array of strings | Paths that must exist before execution. |
| `valid_results` | array | non-empty array of strings | Allowed gate result values. |
| `mode` | string | `ralph_loop`, `once`, `live`, or `resume` | Execution pattern. |

#### Optional Fields

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `readonly` | boolean | `false` | Enforce readonly workspace policy. |
| `report_tag` | string | `report` | XML tag for report extraction. |
| `result_tag` | string | `result` | XML tag for result extraction. |
| `output_path` | string | none | Custom output artifact path template. |
| `completion_check` | string | `result_tag` | Completion check strategy. |
| `session_from` | string | none | Session source for `resume` mode. |
| `supervisor_interval` | integer | `0` | Supervisor frequency. `0` disables supervision. |
| `plan_file` | string | none | Path template to implementation plan. |
| `outputs` | array | `[]` | Output keys exposed to downstream steps. |
| `runtime` | object | `{}` | Runtime adapter preferences. |
| `hooks` | object | `{}` | Deterministic hook declarations. |
| `capabilities` | array | `[]` | Required capabilities. |
| `artifact_contracts` | array | `[]` | Declared artifacts the agent may produce. |

`valid_results` are not limited to `PASS`, `FAIL`, `FIX`, and `SKIP`, but those
remain the standard values and should be used unless a workflow needs a richer
router result.

### 2.3 Prompt Sections

| Section | Required | Modes |
|---------|----------|-------|
| `INDEXER_SYSTEM_PROMPT` | yes | all |
| `INDEXER_USER_PROMPT` | yes | all |
| `INDEXER_CONTINUATION_PROMPT` | no | `ralph_loop`, `live`, `resume` |

The continuation prompt is appended only after the first iteration or when
resuming a prior session.

### 2.4 Variable Interpolation

Variables use `{{name}}` syntax and are rendered by Indexer before runtime
invocation. Missing required variables are validation errors.

#### Path Variables

| Variable | Source | Availability |
|----------|--------|--------------|
| `{{workspace}}` | worker worktree path | all modes |
| `{{worker_dir}}` | worker root under `.indexer/worktrees` | all modes |
| `{{project_dir}}` | target repository root | all modes |
| `{{indexer_dir}}` | target repository `.indexer` path | all modes |
| `{{control_branch}}` | configured control branch name | all modes |

#### Step Context Variables

| Variable | Source |
|----------|--------|
| `{{work_item.id}}` | current work item id |
| `{{work_item.title}}` | current work item title |
| `{{work_item.body}}` | current work item body |
| `{{step_id}}` | current pipeline step id |
| `{{run_id}}` | current pipeline run id |
| `{{node_run_id}}` | current node run id |
| `{{session_id}}` | current runtime session id, if available |

#### Parent Step Variables

| Variable | Source |
|----------|--------|
| `{{parent.step_id}}` | previous completed step id |
| `{{parent.run_id}}` | previous node run id |
| `{{parent.session_id}}` | previous runtime session id |
| `{{parent.result}}` | previous gate result |
| `{{parent.output_dir}}` | exported artifact directory, if materialized |
| `{{parent.report}}` | previous report artifact or exported path |

#### Iteration Variables

| Variable | Source |
|----------|--------|
| `{{iteration}}` | current loop iteration |
| `{{prev_iteration}}` | previous loop iteration |
| `{{output_dir}}` | exported output directory for this agent run |
| `{{supervisor_feedback}}` | latest supervisor feedback |
| `{{plan_file}}` | rendered plan file or plan artifact path |

#### Generated Content Variables

| Variable | Generator |
|----------|-----------|
| `{{context_section}}` | context builder hook |
| `{{git_restrictions}}` | readonly/workspace policy renderer |
| `{{plan_section}}` | plan renderer |
| `{{memory_section}}` | memory/context retrieval hook |
| `{{review_comments_section}}` | change-set review comment renderer |

### 2.5 Conditional Tags

| Tag | Condition |
|-----|-----------|
| `INDEXER_IF_SUPERVISOR` | supervisor feedback is present |
| `INDEXER_IF_ITERATION_ZERO` | `iteration == 0` |
| `INDEXER_IF_ITERATION_NONZERO` | `iteration > 0` |
| `INDEXER_IF_FILE_EXISTS:path` | interpolated path exists |
| `INDEXER_IF_CONTEXT:key` | context key exists and is non-empty |

Processing rules:

1. Variables are interpolated first.
2. Conditions are evaluated second.
3. A true condition preserves content and removes wrapper tags.
4. A false condition removes the whole block.
5. Nested conditions are allowed.

## 3. Execution Modes

### 3.1 `ralph_loop`

`ralph_loop` is retained as the name of the iterative execution pattern.

It consists of:

1. completion check,
2. work phase,
3. summary phase,
4. optional supervisor phase,
5. next iteration with compacted context.

Requirements:

- MUST use system and user prompts.
- SHOULD define a continuation prompt.
- MUST stop when the completion check passes, the agent returns a terminal gate
  result, `max_iterations` is exceeded, or policy cancels the run.
- If `supervisor_interval > 0`, the supervisor runs every N iterations.

Supervisor decisions:

| Decision | Behavior |
|----------|----------|
| `CONTINUE` | Continue with feedback in `{{supervisor_feedback}}`. |
| `STOP` | Stop the loop and extract result. |
| `RESTART` | Reset iteration context with supervisor guidance. |

### 3.2 `once`

Single-shot execution.

- MUST use system and user prompts.
- MUST NOT append continuation prompts.
- SHOULD be used for summarization, simple review, routing, and deterministic
  result extraction.

### 3.3 `live`

Persistent session mode.

- First invocation creates a runtime session record.
- Later invocations resume that session while it remains valid.
- If the runtime session expires, Indexer creates a new session and links it to
  the prior context summary.

### 3.4 `resume`

Resume a prior runtime session.

- MUST specify `session_from`.
- Standard `session_from` values: `parent`, `latest:<agent-type>`,
  `artifact:<artifact-id>`.
- If the selected runtime adapter does not support sessions, the agent must
  either fail validation or run a configured fallback mode.

## 4. Completion Checks

| Type | Declaration | Behavior |
|------|-------------|----------|
| `result_tag` | `completion_check: result_tag` | Extract `<result>VALUE</result>` from runtime text. |
| `status_file` | `completion_check: status_file:path` | Check a materialized checklist or status artifact. |
| `file_exists` | `completion_check: file_exists:{{output_path}}` | Verify a file exists and is non-empty. |
| `hook` | `completion_check: hook:<name>` | Call a deterministic hook. |
| `artifact_schema` | `completion_check: artifact_schema:<kind>` | Validate a declared artifact. |

Completion checks produce structured diagnostics and may produce a gate result.

## 5. Deterministic Hooks

Hooks replace v1's bash-only override layer with a general deterministic extension
model.

### 5.1 Hook Kinds

| Kind | Description |
|------|-------------|
| `module` | Elixir module implementing the hook behaviour. |
| `executable` | External command that receives JSON on stdin and returns JSON on stdout. |
| `shell` | Shell executable. This is a specialization of `executable`. |
| `pipeline` | Deterministic sub-pipeline. |

### 5.2 Hook Input Envelope

```json
{
  "hook": "prepare",
  "agent_id": "engineering.security-audit",
  "work_item": {},
  "worker": {},
  "pipeline_run": {},
  "node_run": {},
  "workspace": {},
  "repository": {},
  "context": {},
  "artifacts": [],
  "config": {}
}
```

### 5.3 Hook Output Envelope

```json
{
  "status": "ok",
  "gate_result": null,
  "context": {},
  "artifacts": [],
  "effects": [],
  "diagnostics": []
}
```

Hook statuses:

| Status | Meaning |
|--------|---------|
| `ok` | Hook completed. |
| `soft_fail` | Hook failed but the pipeline may route around it. |
| `hard_fail` | Current node fails. |

External executable hooks MUST write machine-readable JSON to stdout and
diagnostics to stderr. Invalid JSON is a hard hook failure.

### 5.4 Standard Hook Names

| Hook | Purpose |
|------|---------|
| `prepare` | Build or enrich context before rendering prompts. |
| `before_turn` | Final deterministic check before runtime invocation. |
| `after_event` | Inspect normalized runtime events as they stream. |
| `extract_result` | Convert runtime data into an agent result. |
| `validate_output` | Verify artifacts, workspace state, and result schema. |
| `summarize` | Produce a durable summary for future context. |
| `plan_effects` | Convert output into requested effects. |
| `cleanup` | Cleanup after success, failure, timeout, or cancellation. |

## 6. Agent Lifecycle

The lifecycle phases are preserved from v1:

```text
LOADING -> INIT -> PREREQUISITE_CHECK -> READY -> EXECUTION -> OUTPUT_VALIDATION -> CLEANUP
```

| Phase | Actions | Failure Behavior |
|-------|---------|------------------|
| `LOADING` | Resolve markdown, hooks, config, runtime adapter. | Abort with config error. |
| `INIT` | Create agent run record, register cancellation, allocate runtime/session refs. | Abort with init error. |
| `PREREQUISITE_CHECK` | Validate `required_paths` and capabilities. | Call error hooks and fail node. |
| `READY` | Run `prepare` and `before_turn` hooks. | Continue unless hook policy fails. |
| `EXECUTION` | Invoke runtime or deterministic agent body. | Capture runtime status and events. |
| `OUTPUT_VALIDATION` | Extract result, validate artifacts, write result records. | Call error hooks and route failure. |
| `CLEANUP` | Run cleanup hooks, release leases, finalize artifacts. | Always attempt. |

### 6.1 Top-Level Agent

A top-level agent run is owned by a worker or service. It includes:

- agent run record,
- cancellation handling,
- runtime process supervision,
- workspace policy enforcement,
- violation monitoring,
- full lifecycle hooks.

### 6.2 Sub-Agent

A sub-agent is owned by a parent pipeline step or orchestrator agent. It:

- shares the worker workspace,
- writes separate agent run and event records,
- does not own worker lifecycle state,
- does not register independent process control unless the runtime adapter needs it.

Sub-agents must be visible in JSONL as separate runs linked by `parent_agent_run_id`.

## 7. Execution Pattern API

The v1 runtime function names remain useful as logical operations. Elixir modules
may expose idiomatic names, but the operations must exist.

### 7.1 Single Run

```text
run_agent_once(workspace, system_prompt, user_prompt, output_ref, max_turns, session_id)
```

Runs one model turn or one bounded non-interactive runtime invocation.

### 7.2 Single Run With New Session

```text
run_agent_once_with_session(workspace, system_prompt, user_prompt, output_ref, max_turns, session_id)
```

Creates a named session if the backend supports sessions.

### 7.3 Resume

```text
run_agent_resume(session_id, prompt, output_ref, max_turns)
```

Resumes an existing session. Session-less backends must report unsupported
capability so callers can choose a fallback.

### 7.4 Ralph Loop

```text
run_ralph_loop(workspace, system_prompt, user_prompt_callback, completion_check_callback,
               max_iterations, max_turns, worker_ref, log_prefix)
```

Preserves the v1 work/summary loop:

1. check completion,
2. generate user prompt,
3. run work turn,
4. extract or generate summary,
5. carry summary into next iteration.

### 7.5 Supervised Ralph Loop

```text
run_ralph_loop_supervised(..., supervisor_interval)
```

Runs the same loop with periodic supervisor turns.

## 8. Agent Result Management

Every agent run MUST end with an agent result record, even when the runtime fails.

```json
{
  "agent_run_id": "agent_run_123",
  "agent_type": "engineering.security-audit",
  "status": "success",
  "exit_code": 0,
  "started_at": "2026-05-07T12:00:00Z",
  "completed_at": "2026-05-07T12:15:00Z",
  "duration_seconds": 900,
  "work_item_id": "TASK-001",
  "worker_id": "worker_TASK_001_1",
  "pipeline_run_id": "pipeline_run_123",
  "node_run_id": "node_run_456",
  "iterations_completed": 3,
  "outputs": {
    "gate_result": "PASS"
  },
  "artifacts": [],
  "effects": [],
  "errors": [],
  "metadata": {}
}
```

This record is appended to `agent_runs.jsonl`. Exported result files may be
created for human inspection, but the ledger record is authoritative.

### 8.1 Gate Result Mapping

| Gate Result | Status | Exit Code | Default Jump |
|-------------|--------|-----------|--------------|
| `PASS` | `success` | `0` | `next` |
| `FAIL` | `failure` | `10` | `abort` |
| `FIX` | `partial` | `0` | `prev` |
| `SKIP` | `success` | `0` | `next` |
| `UNKNOWN` | `unknown` | `1` | `self` |

Agents may extend this mapping through their config.

### 8.2 Result Operations

The following v1 functions become logical APIs:

| V1 Function | V2 Operation |
|-------------|--------------|
| `agent_write_result` | append an `agent_runs.jsonl` completion record. |
| `agent_write_report` | append an artifact record and optionally export markdown. |
| `agent_read_subagent_result` | query latest linked agent result by type or run id. |
| `agent_find_latest_result` | query projection for latest result. |
| `agent_find_latest_report` | query artifact projection for latest report. |
| `agent_extract_and_write_result` | run `extract_result` hook and append result. |

The operations must be exposed to Elixir hooks directly and to external hooks via
the JSON hook envelope.

## 9. Configuration

### 9.1 Agent Registry Configuration

```json
{
  "agents": {
    "engineering.security-audit": {
      "definition": "config/agents/engineering/security-audit.md",
      "max_iterations": 8,
      "max_turns": 30,
      "timeout_seconds": 3600,
      "runtime": {
        "adapter": "codex"
      },
      "result_mappings": {}
    }
  },
  "defaults": {
    "max_iterations": 20,
    "max_turns": 50,
    "timeout_seconds": 10800,
    "result_mappings": {}
  }
}
```

### 9.2 Configuration Precedence

Highest priority first:

1. explicit pipeline step `config`,
2. operator CLI/API override,
3. environment variables with `INDEXER_` prefix,
4. project config under `.indexer/config.json`,
5. control-branch config,
6. built-in `config/agents.json`,
7. hardcoded defaults.

Configuration used for an agent run is copied into the `agent_runs.jsonl` start
record so replay and debugging are stable.

## 10. Capabilities

Agents declare required capabilities:

| Capability | Meaning |
|------------|---------|
| `workspace_read` | Read assigned workspace. |
| `workspace_write` | Modify assigned workspace. |
| `git_read` | Run git read operations. |
| `git_write_work_branch` | Commit/rebase within worker branch. |
| `git_merge` | Request merge effects. |
| `control_branch_read` | Read control branch records. |
| `control_branch_write` | Request control branch write effects. |
| `network` | Use network through runtime or hooks. |
| `shell` | Execute shell commands. |
| `browser` | Use browser automation. |
| `secrets` | Access configured secrets. |

Capabilities are granted by pipeline policy and runtime adapter policy. Prompt text
cannot grant capabilities.

## 11. Readonly Agent Constraints

When `readonly: true`, agents MUST NOT:

- create, modify, or delete workspace files,
- run git write operations,
- stage, commit, merge, rebase, or push,
- modify tracked files through hooks.

Readonly agents MAY:

- read files,
- run git read operations,
- append JSONL state through Indexer,
- write logs, reports, summaries, and artifacts outside the workspace,
- request effects if pipeline policy allows them.

The `{{git_restrictions}}` generated variable MUST be included in rendered system
context for readonly model-facing agents.

## 12. Worker Directory Structure

Indexer workers use `.indexer`, not `.ralph`:

```text
.indexer/worktrees/worker-TASK-001-1/
├── workspace/              # Git worktree
├── work_item.md            # Rendered work item, optional export
├── live_sessions/          # Runtime session refs, optional projection
├── logs/                   # Raw exported logs, optional artifacts
├── results/                # Exported result JSONs, optional artifacts
├── reports/                # Exported reports
├── summaries/              # Exported iteration summaries
└── output/
    └── <agent-type>/
```

Authoritative state is under `.indexer/state/*.jsonl`. Files in the worker
directory are workspace content, operator convenience exports, or large artifacts.

## 13. Validation Requirements

### 13.1 Frontmatter Validation

The loader MUST verify:

- all required fields are present,
- `type` matches the dotted-name pattern,
- `mode` is one of the supported modes,
- `valid_results` is non-empty,
- `required_paths` is non-empty,
- `resume` mode has `session_from`,
- prompt sections required by mode are present,
- hooks resolve and declare failure behavior.

### 13.2 Prerequisite Validation

Before execution, Indexer MUST verify:

- all required paths exist,
- paths remain within the worker or project boundary,
- required capabilities are granted,
- runtime adapter is available,
- readonly/write policy is satisfiable.

### 13.3 Output Validation

After execution, Indexer MUST verify:

- an agent result record can be produced,
- `outputs.gate_result` is present or intentionally `UNKNOWN`,
- gate result is allowed by `valid_results` or mapped by config,
- required artifacts exist and pass declared schemas,
- requested effects have idempotency keys,
- readonly workspace constraints were not violated.

## Appendix A: Built-In Agent Families

The exact default set may change, but these v1 families should be preserved as
reference categories:

| Family | Examples | Purpose |
|--------|----------|---------|
| `system` | `task-worker`, `resume-decide`, `failure-resolver` | Orchestration and recovery. |
| `engineering` | `software-engineer`, `security-audit`, `security-fix`, `test-coverage`, `validation-review`, `git-conflict-resolver` | Code implementation, review, testing, and repair. |
| `product` | `plan-mode`, `system-architect` | Planning and design. |
| `general` | `task-summarizer`, `documentation-writer`, `domain-expert` | General-purpose summarization and documentation. |
| `workflow` | `git-sync-main`, `git-commit-push`, `batch-*` | Deterministic or mostly deterministic workflow steps. |

GitHub-specific agents from v1 should be generalized into git-native change-set,
review-comment, and control-branch agents or hooks.

## Appendix B: Exit Codes

Indexer keeps the v1 result code meanings for CLI compatibility at the semantic
level:

| Code | Meaning |
|------|---------|
| `0` | Success or `PASS`. |
| `1` | General or unknown error. |
| `2` | Invalid arguments. |
| `3` | Configuration error. |
| `4` | Git error. |
| `5` | Runtime adapter error. |
| `10` | Agent `FAIL` result. |
| `12` | Max iterations exceeded. |

Runtime adapters may have backend-specific process exit codes, but those must be
normalized before pipeline routing.
