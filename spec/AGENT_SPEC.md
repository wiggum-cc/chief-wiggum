# Agent Specification

**Version:** 1.0  
**Status:** Normative

This document specifies the agent interface, lifecycle, and configuration contracts for Chief Wiggum. Implementations MUST conform to the requirements defined herein.

## Terminology

The keywords "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119).

---

## 1. Agent Classification

### 1.1 Agent Formats

Agents MUST be implemented in one of two formats:

| Format | Extension | Interpreter | Priority |
|--------|-----------|-------------|----------|
| Declarative Markdown | `.md` | `lib/core/agent-md.sh` | Base |
| Shell Script | `.sh` | Direct execution | Override |

When both `.md` and `.sh` files exist for the same agent name:
1. The markdown definition MUST load first (base behavior)
2. The shell script MUST load second and MAY override any function

### 1.2 Agent Categories

| Category | Location | Characteristics |
|----------|----------|-----------------|
| Orchestrator | `lib/agents/system/` | Manages pipeline, spawns sub-agents, MUST NOT call `claude/*` directly |
| Leaf | `lib/agents/*/` | Single-task execution, invoked via `run_sub_agent` |

---

## 2. Declarative Markdown Agent Specification

### 2.1 File Structure

A markdown agent file MUST contain:
1. YAML frontmatter delimited by `---`
2. At least one prompt section (`<WIGGUM_SYSTEM_PROMPT>`, `<WIGGUM_USER_PROMPT>`)

### 2.2 Frontmatter Schema

#### 2.2.1 Required Fields

| Field | Type | Constraints | Description |
|-------|------|-------------|-------------|
| `type` | string | Pattern: `[a-z]+\.[a-z-]+` | Agent type identifier |
| `description` | string | Non-empty | Human-readable description |
| `required_paths` | array | Non-empty array of strings | Paths that MUST exist before execution |
| `valid_results` | array | Subset of `[PASS, FAIL, FIX, SKIP]` | Allowed result values |
| `mode` | string | One of: `ralph_loop`, `once`, `live`, `resume` | Execution mode |

#### 2.2.2 Optional Fields

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `readonly` | boolean | `false` | Inject git restrictions when `true` |
| `report_tag` | string | `report` | XML tag for report extraction |
| `result_tag` | string | `result` | XML tag for result extraction |
| `output_path` | string | - | Custom output file path (supports variables) |
| `completion_check` | string | `result_tag` | Completion check strategy |
| `session_from` | string | - | Session source for `resume` mode |
| `supervisor_interval` | integer | `0` | Supervisor frequency (0 = disabled) |
| `plan_file` | string | - | Path template to implementation plan |
| `outputs` | array | - | Output keys exposed to downstream steps |

### 2.3 Prompt Sections

| Section | Required | Modes |
|---------|----------|-------|
| `<WIGGUM_SYSTEM_PROMPT>` | YES | All |
| `<WIGGUM_USER_PROMPT>` | YES | All |
| `<WIGGUM_CONTINUATION_PROMPT>` | NO | `ralph_loop` only |

The continuation prompt section MUST only be appended when `iteration > 0`.

### 2.4 Variable Interpolation

Variables use `{{name}}` syntax and MUST be replaced at runtime.

#### 2.4.1 Path Variables

| Variable | Source | Availability |
|----------|--------|--------------|
| `{{workspace}}` | `$worker_dir/workspace` | All modes |
| `{{worker_dir}}` | Argument 1 to `agent_run()` | All modes |
| `{{project_dir}}` | Argument 2 to `agent_run()` | All modes |
| `{{ralph_dir}}` | `$RALPH_DIR` or `$PROJECT_DIR/.ralph` | All modes |

#### 2.4.2 Step Context Variables

| Variable | Source | Availability |
|----------|--------|--------------|
| `{{task_id}}` | Extracted from worker_dir | All modes |
| `{{step_id}}` | `$WIGGUM_STEP_ID` | All modes |
| `{{run_id}}` | `$RALPH_RUN_ID` | All modes |
| `{{session_id}}` | Generated per-iteration | All modes |

#### 2.4.3 Parent Step Variables

| Variable | Source |
|----------|--------|
| `{{parent.step_id}}` | `$WIGGUM_PARENT_STEP_ID` |
| `{{parent.run_id}}` | `$WIGGUM_PARENT_RUN_ID` |
| `{{parent.session_id}}` | Parent result outputs |
| `{{parent.result}}` | `$WIGGUM_PARENT_RESULT` |
| `{{parent.output_dir}}` | Computed from parent run_id |
| `{{parent.report}}` | `$WIGGUM_PARENT_REPORT` |

#### 2.4.4 Iteration Variables (ralph_loop mode)

| Variable | Source |
|----------|--------|
| `{{iteration}}` | Callback argument 1 |
| `{{prev_iteration}}` | `iteration - 1` |
| `{{output_dir}}` | Callback argument 2 |
| `{{supervisor_feedback}}` | Supervisor output (empty if none) |
| `{{plan_file}}` | `$WIGGUM_PLAN_FILE` or default |

#### 2.4.5 Generated Content Variables

| Variable | Generator |
|----------|-----------|
| `{{context_section}}` | `_md_generate_context_section()` |
| `{{git_restrictions}}` | `_md_generate_git_restrictions()` |
| `{{plan_section}}` | `_md_generate_plan_section()` |

### 2.5 Conditional Tags

| Tag | Condition |
|-----|-----------|
| `<WIGGUM_IF_SUPERVISOR>` | Supervisor feedback is present |
| `<WIGGUM_IF_ITERATION_ZERO>` | `iteration == 0` |
| `<WIGGUM_IF_ITERATION_NONZERO>` | `iteration > 0` |
| `<WIGGUM_IF_FILE_EXISTS:path>` | Interpolated path exists |

Processing rules:
1. Tags MUST be processed after variable interpolation
2. When condition is true: content is preserved, tags are removed
3. When condition is false: entire block including content is removed
4. Tags MAY be nested; inner conditions are evaluated after outer

### 2.6 Execution Modes

#### 2.6.1 Mode: `ralph_loop`

Iterative execution with optional supervision.

- MUST use all three prompt sections
- Continuation prompt MUST only append when `iteration > 0`
- If `supervisor_interval > 0`, supervisor MUST run every N iterations

Supervisor responses:
| Response | Behavior |
|----------|----------|
| `CONTINUE` | Proceed with feedback via `{{supervisor_feedback}}` |
| `STOP` | Halt the loop |
| `RESTART` | Reset iteration to 0 with guidance |

#### 2.6.2 Mode: `once`

Single-shot execution.

- MUST use system prompt and user prompt only
- MUST NOT use continuation prompt

#### 2.6.3 Mode: `live`

Persistent session mode.

- First invocation MUST generate UUID and create session file at `$worker_dir/live_sessions/{step_id}.session`
- Subsequent invocations MUST resume existing session
- On session expiry, MUST automatically create new session

#### 2.6.4 Mode: `resume`

Resume a prior Claude session.

- MUST specify `session_from` in frontmatter
- Valid `session_from` values: `parent`

### 2.7 Completion Check Types

| Type | Declaration | Behavior |
|------|-------------|----------|
| `result_tag` | `completion_check: result_tag` | Extract `<result>VALUE</result>` from logs |
| `status_file` | `completion_check: status_file:path` | Check for `- [ ]` items in file |
| `file_exists` | `completion_check: file_exists:{{output_path}}` | Verify output file exists and is non-empty |

---

## 3. Shell Script Agent Specification

### 3.1 Required Header

```bash
#!/usr/bin/env bash
set -euo pipefail
```

### 3.2 Metadata Block

Shell agents MUST include a metadata comment block:

```bash
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: <agent-type>
# AGENT_DESCRIPTION: <description>
# REQUIRED_PATHS:
#   - <path> : <description>
# =============================================================================
```

### 3.3 Required Functions

#### 3.3.1 `agent_required_paths()`

MUST echo space-separated list of required paths relative to worker_dir.

```bash
agent_required_paths() {
    echo "workspace"
}
```

#### 3.3.2 `agent_run(worker_dir, project_dir)`

MUST implement the main agent execution logic.

| Argument | Type | Description |
|----------|------|-------------|
| `worker_dir` | string | Worker directory path |
| `project_dir` | string | Original project root path |

Return codes:
| Code | Meaning |
|------|---------|
| 0 | Success (PASS) |
| 10 | Failure (FAIL) |
| 12 | Max iterations exceeded |

### 3.4 Optional Lifecycle Hooks

| Hook | Signature | Invocation Point |
|------|-----------|------------------|
| `agent_on_init` | `(worker_dir, project_dir)` | Before PID file creation |
| `agent_on_ready` | `(worker_dir, project_dir)` | After init, before `agent_run` |
| `agent_on_error` | `(worker_dir, exit_code, error_type)` | On validation/prerequisite failure |
| `agent_on_signal` | `(signal)` | On INT/TERM signal before cleanup |
| `agent_cleanup` | `(worker_dir)` | After `agent_run` completes |

The `error_type` argument MUST be one of: `prereq`, `output`.

---

## 4. Agent Lifecycle

### 4.1 Lifecycle Phases

```
LOADING → INIT → PREREQUISITE_CHECK → READY → EXECUTION → OUTPUT_VALIDATION → CLEANUP
```

### 4.2 Phase Requirements

| Phase | Actions | Failure Behavior |
|-------|---------|------------------|
| LOADING | Source agent script | Abort with exit code 1 |
| INIT | Create PID file, register signal handlers | Abort with exit code 1 |
| PREREQUISITE_CHECK | Validate `agent_required_paths()` | Call `agent_on_error`, abort |
| READY | Call `agent_on_ready()` | Continue to EXECUTION |
| EXECUTION | Call `agent_run()` | Capture exit code |
| OUTPUT_VALIDATION | Verify epoch-named result JSON | Call `agent_on_error` if invalid |
| CLEANUP | Call `agent_cleanup()`, remove PID file | Always execute |

### 4.3 PID File Management

- Location: `$worker_dir/agent.pid`
- MUST be created in INIT phase
- MUST be removed in CLEANUP phase
- Sub-agents MUST NOT manage PID files

### 4.4 Signal Handling

- Agents MUST register handlers for: `INT`, `TERM`
- Signal handlers MUST call `agent_on_signal()` if defined
- Signal handlers MUST proceed to CLEANUP phase

---

## 5. Execution Patterns

### 5.1 Unsupervised Ralph Loop

Signature:
```bash
run_ralph_loop "$workspace" "$system_prompt" "user_prompt_fn" "completion_check_fn" \
    "$max_iterations" "$max_turns" "$worker_dir" "$log_prefix"
```

| Arg | Type | Description |
|-----|------|-------------|
| 1 | string | Workspace directory |
| 2 | string | System prompt |
| 3 | string | User prompt callback function name |
| 4 | string | Completion check callback function name |
| 5 | integer | Maximum iterations |
| 6 | integer | Maximum turns per session |
| 7 | string | Worker directory |
| 8 | string | Log filename prefix |

User prompt callback signature (unsupervised):
```bash
fn(iteration, output_dir)
```

### 5.2 Supervised Ralph Loop

Signature:
```bash
run_ralph_loop_supervised "$workspace" "$system_prompt" "user_prompt_fn" "completion_check_fn" \
    "$max_iterations" "$max_turns" "$worker_dir" "$log_prefix" "$supervisor_interval"
```

Additional argument:
| Arg | Type | Description |
|-----|------|-------------|
| 9 | integer | Supervisor interval |

User prompt callback signature (supervised):
```bash
fn(iteration, output_dir, supervisor_dir, supervisor_feedback)
```

### 5.3 Single-Run Execution

Signature:
```bash
run_agent_once "$workspace" "$system_prompt" "$user_prompt" "$log_file" "$max_turns"
```

| Arg | Type | Description |
|-----|------|-------------|
| 1 | string | Workspace directory |
| 2 | string | System prompt |
| 3 | string | User prompt (string, not callback) |
| 4 | string | Log file path |
| 5 | integer | Maximum turns |

### 5.4 Completion Check Callback

Signature:
```bash
fn() -> exit_code
```

| Return | Meaning |
|--------|---------|
| 0 | Work complete, exit loop |
| non-zero | Continue iteration |

---

## 6. Invocation Modes

### 6.1 Top-Level Agent (`run_agent`)

```bash
run_agent "$agent_type" "$worker_dir" "$project_dir"
```

Includes:
- PID file management
- Signal handling
- Violation monitoring
- Full lifecycle hooks

### 6.2 Sub-Agent (`run_sub_agent`)

```bash
run_sub_agent "$agent_type" "$worker_dir" "$project_dir"
```

Excludes:
- PID file management
- Signal handling
- Violation monitoring

MUST only execute `agent_run()`.

---

## 7. Result Management

### 7.1 Result File Specification

Path: `$worker_dir/results/<epoch>-<agent-type>-result.json`

Schema:
```json
{
  "agent_type": "string",
  "status": "success|failure|partial|unknown",
  "exit_code": "integer",
  "started_at": "ISO 8601 timestamp",
  "completed_at": "ISO 8601 timestamp",
  "duration_seconds": "integer",
  "task_id": "string",
  "worker_id": "string",
  "iterations_completed": "integer",
  "outputs": {
    "gate_result": "PASS|FAIL|FIX|SKIP"
  },
  "errors": ["string"],
  "metadata": {}
}
```

### 7.2 Gate Result Mapping

| gate_result | status | exit_code | default_jump |
|-------------|--------|-----------|--------------|
| `PASS` | success | 0 | next |
| `FAIL` | failure | 10 | abort |
| `FIX` | partial | 0 | prev |
| `SKIP` | success | 0 | next |

### 7.3 Result Functions

| Function | Signature | Description |
|----------|-----------|-------------|
| `agent_write_result` | `(worker_dir, gate_result, [extra_outputs], [errors])` | Write epoch-named result JSON |
| `agent_write_report` | `(worker_dir, content)` | Write epoch-named report, returns path |
| `agent_read_subagent_result` | `(worker_dir, agent_name)` | Read gate_result from sub-agent |
| `agent_find_latest_result` | `(worker_dir, agent_type)` | Find latest result file path |
| `agent_find_latest_report` | `(worker_dir, agent_type)` | Find latest report file path |
| `agent_get_result_path` | `(worker_dir)` | Get result path for current agent |
| `agent_extract_and_write_result` | `(worker_dir, name, log_prefix, report_tag, valid_values)` | Extract from logs and write |

### 7.4 Output Directory Constraints

Agents MUST NOT delete files from:
- `$worker_dir/logs/`
- `$worker_dir/results/`
- `$worker_dir/reports/`
- `$worker_dir/summaries/`

Agents MUST only append new epoch-named entries.

---

## 8. Configuration

### 8.1 Agent Registry Configuration

Location: `config/agents.json`

Schema:
```json
{
  "agents": {
    "<agent-type>": {
      "max_iterations": "integer",
      "max_turns": "integer",
      "timeout_seconds": "integer",
      "result_mappings": {}
    }
  },
  "defaults": {
    "max_iterations": "integer",
    "max_turns": "integer",
    "timeout_seconds": "integer",
    "result_mappings": {}
  }
}
```

### 8.2 Configuration Precedence

1. Environment variable: `WIGGUM_{AGENT_NAME}_MAX_TURNS`
2. Agent-specific config: `config/agents.json`.agents.<agent-type>
3. Default config: `config/agents.json`.defaults
4. Hardcoded default

Environment variable naming: `WIGGUM_{AGENT_NAME}_{PARAM}` where `AGENT_NAME` is uppercase with hyphens replaced by underscores.

### 8.3 Orchestrator Parameters

Orchestrator agents receive positional arguments:

| Arg | Default Source | Description |
|-----|----------------|-------------|
| 3 | `$AGENT_CONFIG_MAX_ITERATIONS` | Maximum iterations |
| 4 | `$AGENT_CONFIG_MAX_TURNS` | Maximum turns |
| 5 | `"execution"` | Start-from step for resume |
| 6 | - | Resume instructions file path |

---

## 9. Agent Base Library

### 9.1 Required Initialization

```bash
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "<agent-name>" "<description>"
```

### 9.2 Dependency Sourcing Functions

| Function | Provides |
|----------|----------|
| `agent_source_core` | logger, defaults, exit-codes |
| `agent_source_ralph` | unsupervised ralph loop |
| `agent_source_ralph_supervised` | supervised ralph loop |
| `agent_source_once` | single-run execution |
| `agent_source_resume` | session resume support |
| `agent_source_violations` | workspace violation monitoring |
| `agent_source_tasks` | task/PRD parser |
| `agent_source_git` | git operations |
| `agent_source_lock` | file locking primitives |
| `agent_source_metrics` | metrics collection |
| `agent_source_registry` | agent registry lookups |

### 9.3 Context Setup

Orchestrator agents (with task ID):
```bash
agent_setup_context "$worker_dir" "$workspace" "$project_dir" "$task_id"
```

Leaf/sub-agents:
```bash
agent_setup_context "$worker_dir" "$workspace" "$project_dir"
```

Context variables set:
| Variable | Description |
|----------|-------------|
| `$AGENT_WORKER_DIR` | Worker directory |
| `$AGENT_WORKSPACE` | Workspace path |
| `$AGENT_PROJECT_DIR` | Project directory |
| `$AGENT_TASK_ID` | Task ID (empty for leaf agents) |

### 9.4 Memory Context

```bash
agent_get_memory_context                  # Uses $_AGENT_PROJECT_DIR
agent_get_memory_context "$project_dir"   # Explicit directory
```

Returns formatted memory section or empty string.

Markdown agents receive memory via `{{context_section}}` automatically.

---

## 10. Readonly Agent Constraints

When `readonly: true`:

Agents MUST NOT:
- Create, modify, or delete files in the workspace
- Execute git write operations (commit, push, merge, rebase)
- Modify any tracked files

Agents MAY:
- Read any file
- Execute git read operations (status, log, diff)
- Write to output directories (`logs/`, `results/`, `reports/`)

The `{{git_restrictions}}` variable MUST be included in system prompts for readonly agents.

---

## 11. Worker Directory Structure

```
$worker_dir/
├── workspace/           # Git worktree
├── prd.md              # Product requirements document
├── activity.jsonl      # Event log (NDJSON)
├── agent.pid           # PID file (top-level agents only)
├── gate_result         # Last gate result
├── live_sessions/      # Live mode session files
│   └── {step_id}.session
├── logs/               # Agent execution logs
├── results/            # Epoch-named result JSONs
├── reports/            # Epoch-named reports
├── summaries/          # Iteration summaries
└── output/             # Per-agent output directories
    └── {agent}/
```

---

## 12. Exit Codes

| Code | Constant | Meaning |
|------|----------|---------|
| 0 | `EXIT_SUCCESS` | Success/PASS |
| 1 | `EXIT_ERROR` | General error |
| 2 | `EXIT_INVALID_ARGS` | Invalid arguments |
| 3 | `EXIT_CONFIG_ERROR` | Configuration error |
| 4 | `EXIT_GIT_ERROR` | Git error |
| 5 | `EXIT_CLAUDE_ERROR` | Claude error |
| 10 | `EXIT_AGENT_FAIL` | Agent FAIL result |
| 12 | `EXIT_MAX_ITERATIONS` | Max iterations exceeded |

---

## 13. Validation Requirements

### 13.1 Prerequisite Validation

Before EXECUTION phase, the runtime MUST verify:
1. All paths returned by `agent_required_paths()` exist
2. Paths are relative to `$worker_dir`

On failure: call `agent_on_error(worker_dir, exit_code, "prereq")` and abort.

### 13.2 Output Validation

After EXECUTION phase, the runtime MUST verify:
1. Epoch-named result JSON exists in `$worker_dir/results/`
2. Result JSON is valid JSON
3. Result JSON contains required fields: `agent_type`, `status`, `exit_code`, `outputs.gate_result`

On failure: call `agent_on_error(worker_dir, exit_code, "output")`.

### 13.3 Frontmatter Validation (Markdown Agents)

The interpreter MUST validate:
1. All required fields are present
2. `type` matches pattern `[a-z]+\.[a-z-]+`
3. `mode` is one of: `ralph_loop`, `once`, `live`, `resume`
4. `valid_results` contains only: `PASS`, `FAIL`, `FIX`, `SKIP`
5. `resume` mode has `session_from` specified

---

## Appendix A: Agent Valid Results by Type

| Agent | Valid Results |
|-------|---------------|
| `engineering.security-audit` | PASS, FIX, FAIL |
| `engineering.security-fix` | PASS, FIX, FAIL |
| `engineering.generic-fix` | PASS, FIX, FAIL |
| `engineering.validation-review` | PASS, FAIL |
| `engineering.test-coverage` | PASS, FIX, FAIL, SKIP |
| `product.plan-mode` | PASS, FAIL |
| `system.task-summarizer` | PASS, SKIP |

---

## Appendix B: Built-in Agents Reference

### B.1 Orchestrator Agents

| Agent | Description |
|-------|-------------|
| `system.task-worker` | Main task execution, manages pipeline and sub-agents |

### B.2 Leaf Agents

| Agent | Mode | Description |
|-------|------|-------------|
| `engineering.software-engineer` | ralph_loop_supervised | Main code-writing agent |
| `system.task-summarizer` | resume | Final summary generation |
| `system.resume-decide` | once | Analyze logs for resume decision |
| `product.plan-mode` | ralph_loop | Read-only exploration and planning |
| `product.documentation-writer` | once | Documentation updates |
| `engineering.validation-review` | ralph_loop | Code review against PRD |
| `engineering.security-audit` | ralph_loop | Security vulnerability scanning |
| `engineering.security-fix` | ralph_loop | Security vulnerability fixes |
| `engineering.test-coverage` | ralph_loop | Test generation |
| `engineering.code-review` | ralph_loop | Code quality review |
| `engineering.git-conflict-resolver` | ralph_loop | Merge conflict resolution |
| `engineering.pr-comment-fix` | ralph_loop | PR review comment fixes |
