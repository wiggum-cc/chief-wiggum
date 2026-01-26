# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Chief Wiggum is an autonomous task runner that orchestrates workers to execute software engineering tasks using Claude Code. It parses tasks from a Kanban board (`.ralph/kanban.md`), spawns isolated workers via git worktrees, runs multi-stage pipelines of specialized agents, and creates pull requests.

**Language**: Bash 4.0+ with Python TUI component

## Commands

### Running Tests
```bash
./tests/test-runner.sh                      # Run all Bash tests
./tests/test-runner.sh --filter <pattern>   # Run filtered tests
./tests/run-all-tests.sh                    # Run ALL tests (Bash + TUI)
./tests/run-all-tests.sh --quick            # Quick mode (skip slow tests)
./tests/tui-test-runner.sh                  # Run TUI tests only
./tests/run-coverage.sh                     # Code coverage
./tests/run-shellcheck.sh                   # Bash linting
bash tests/test_<name>.sh                   # Run specific test file
```

### Development
```bash
export WIGGUM_HOME=$(pwd)
export PATH="$WIGGUM_HOME/bin:$PATH"
```

### Debugging
```bash
wiggum inspect worker TASK-001              # Inspect worker state
wiggum inspect pipeline                     # Show pipeline config
wiggum inspect agents                       # List agents
wiggum inspect activity [TASK-ID]           # View activity logs
WIGGUM_LOG_LEVEL=debug wiggum run           # Verbose logging
```

## Architecture

### Directory Structure

| Directory | Purpose |
|-----------|---------|
| `bin/` | CLI entry points (15 command scripts) |
| `lib/core/` | Shared utilities (logger, exit codes, file locking, preflight) |
| `lib/claude/` | Claude Code invocation patterns |
| `lib/agents/` | Agent implementations (system, engineering, product) |
| `lib/pipeline/` | Pipeline engine (loader, runner - state machine) |
| `lib/worker/` | Worker lifecycle management |
| `lib/tasks/` | Kanban parsing, task parsing |
| `lib/git/` | Git worktree operations, PR creation |
| `lib/utils/` | Logging, metrics, cost calculation |
| `config/` | Pipeline, agents, and schema definitions (JSON) |
| `docs/` | Architecture, pipeline schema, agent dev guide, protocol |
| `tests/` | Test suite (35+ test files) |
| `skills/` | Claude Code skill definitions |
| `tui/` | Python Textual-based monitoring UI |

### Claude Invocation Patterns (`lib/claude/`)

1. **run-claude-once.sh** - Single-shot execution, no session continuity
2. **run-claude-ralph-loop.sh** - Unified iterative loop with optional supervision
   - `supervisor_interval=0` (default): Pure iterative loop with summaries
   - `supervisor_interval=N`: Supervisor reviews every N iterations (CONTINUE/STOP/RESTART)

### Pipeline Engine

Jump-based state machine defined in `config/pipeline.json`. Steps have `on_result` handlers (PASS/FAIL/FIX/SKIP) controlling flow via jump targets: `self`, `prev`, `next`, `abort`, or step ID.

Default pipeline: planning → execution (supervised) → summary → audit → audit-fix → test → docs → validation

### Agent Architecture

All agents source `lib/core/agent-base.sh` and implement:
```bash
agent_run(worker_dir, project_dir)
# Returns: 0=PASS, 10=FAIL, 12=MAX_ITERATIONS
```

**Agent Categories**:
- `lib/agents/system/` - task-worker, task-summarizer, resume-decide
- `lib/agents/engineering/` - software-engineer, security-audit, security-fix, test-coverage, validation-review
- `lib/agents/product/` - plan-mode, documentation-writer

### Worker Structure

Each worker operates in `.ralph/workers/worker-TASK-XXX-<timestamp>/` with:
- `workspace/` - Git worktree
- `prd.md` - Generated requirements
- `activity.jsonl` - Event log (NDJSON)
- `output/<agent>/` - Per-agent outputs
- `gate_result` - Last agent result (PASS/FAIL/FIX/SKIP)

### Exit Codes (`lib/core/exit-codes.sh`)

| Code | Meaning |
|------|---------|
| 0 | Success/PASS |
| 1 | General error |
| 2 | Invalid arguments |
| 3 | Configuration error |
| 4 | Git error |
| 5 | Claude error |
| 10 | Agent FAIL |
| 12 | Max iterations exceeded |

### Configuration

- `config/pipeline.json` - Default pipeline definition
- `config/agents.json` - Agent registry with iteration/turn limits and per-agent result_mappings
- `.ralph/config.json` - Project-specific overrides
- `.ralph/pipeline.json` - Project pipeline override
- `.ralph/pipelines/<TASK-ID>.json` - Task-specific pipeline

### Kanban Format (`.ralph/kanban.md`)

**Specification**: `skills/kanban/references/task-format.md`

```markdown
- [ ] **[TASK-001]** Brief description
  - Description: Detailed explanation
  - Priority: CRITICAL|HIGH|MEDIUM|LOW
  - Dependencies: TASK-002, TASK-003 | none
```

**Easy to get wrong**:
- Task ID pattern: `[A-Za-z]{2,10}-[0-9]{1,4}` (prefix 2-10 letters, number 1-4 digits)
- Fields must be 2-space indented under task line
- Priority and Dependencies are **required**
- Only `[x]` (Complete) satisfies dependencies - `[P]` does NOT
- Status markers: `[ ]` Pending, `[=]` In-progress, `[P]` Pending approval, `[x]` Complete, `[*]` Failed, `[N]` Not planned

### Task Prioritization

Tasks are sorted by effective priority using fixed-point arithmetic (10000 = 1.0000):

| Priority | Value | Decimal |
|----------|-------|---------|
| CRITICAL | 0 | 0.0 |
| HIGH | 10000 | 1.0 |
| MEDIUM | 20000 | 2.0 |
| LOW | 30000 | 3.0 |

**Bonuses (subtract from priority)**:
| Modifier | Value | Condition |
|----------|-------|-----------|
| Plan bonus | -15000 (-1.5) | Task has `.ralph/plans/<TASK-ID>.md` |
| Aging bonus | -8000/level (-0.8) | Per `AGING_FACTOR` (7) scheduling events waiting |
| Dependency bonus | -7000/task (-0.7) | Per task transitively blocked by this one |

**Penalties (add to priority)**:
| Modifier | Formula | Example |
|----------|---------|---------|
| Sibling WIP | `sqrt(N) * 20000` | N=1: +20000, N=4: +40000 |

**Example calculation**:
- HIGH task with plan, blocking 3 tasks, 1 sibling WIP:
  - Base: 10000
  - Plan: -15000
  - Dep bonus: -21000 (3 × 7000)
  - Sibling: +20000
  - **Effective: -6000 → 0** (floored)

## Testing Patterns

Test framework uses custom assertions:
```bash
assert_exit_code 0
assert_equals "expected" "$actual"
assert_match "regex" "$output"
assert_file_exists "/path"
```

## Documentation

| Document | Purpose |
|----------|---------|
| `docs/ARCHITECTURE.md` | Developer guide, component overview, internals |
| `docs/PIPELINE-SCHEMA.md` | Pipeline configuration schema and step definitions |
| `docs/AGENT_DEV_GUIDE.md` | Writing custom agents, lifecycle hooks |
| `docs/PROTOCOL.md` | Inter-agent communication, data passing mechanisms |
| `docs/AUDIT_LOG.md` | Security audit trail format and events |

## Bash Coding Style

### Script Header
```bash
#!/usr/bin/env bash
set -euo pipefail
```

### Double-Source Prevention
```bash
[ -n "${_MODULE_LOADED:-}" ] && return 0
_MODULE_LOADED=1
```

### Variables
- Always quote variables: `"$var"` not `$var`
- Use `${var:-default}` for defaults
- Use `local` for function variables: `local foo="bar"`
- Declare associative arrays: `local -A map=()`

### Arithmetic
- Use `(( ))` for arithmetic: `((++count))`, `((i + 1))`
- Add `|| true` when increment might be 0 under `set -e`: `((count++)) || true`

### Conditionals
- Use `[[ ]]` for tests: `[[ -n "$var" ]]`, `[[ "$a" == "$b" ]]`
- Use `[ ]` only for simple existence checks in one-liners: `[ -n "${VAR:-}" ] && return 0`

### Functions
```bash
# Brief description of what the function does
#
# Args:
#   arg1 - Description
#   arg2 - Description
#
# Returns: exit code or echoes value
function_name() {
    local arg1="$1"
    local arg2="$2"
    ...
}
```

### Shellcheck
- Run `./tests/run-shellcheck.sh` before committing
- All scripts must pass shellcheck
- Use `# shellcheck disable=SC####` with justification when necessary

## Python TUI Development

The TUI component uses Python 3.10+ with [uv](https://docs.astral.sh/uv/) for dependency management.

## Critical Constraints & Gotchas

### Agent Rules
- **Orchestrators never call `claude/*` directly** - they delegate via `run_sub_agent`
- **Sub-agents don't manage PID files or signal handlers** - only top-level agents do
- **`readonly: true` agents get git checkpoint restored after exit** - changes are discarded
- **Agents must write epoch-named results** - use `agent_write_result`, never delete from `results/`, `reports/`, `logs/`, `summaries/`
- **Ralph loop callbacks use unified 4-arg signature**: `user_prompt_fn(iteration, output_dir, supervisor_dir, supervisor_feedback)` - agents not using supervision can ignore the last 2 args

### Pipeline Rules
- **Every cycle needs a bounded `max`** - termination guarantee requires `max` on any step in a loop
- **Unhandled results use `default_jump` from result_mappings** - explicit handlers needed for custom behavior
- **Inline agent handlers implicitly jump to parent (`prev`)** after completion
- **`on_max` default is `next`** - pipeline continues even if step hit iteration limit

### Concurrency
- **Always use `flock` for shared resources** - kanban, PID files, event logs
- **Worker directory is the namespace boundary** - all inter-agent state scoped here
- **Epoch naming prevents collisions** - multiple runs of same agent produce distinct files

### Gate Result Values (easy to forget)
| Agent | Possible Values |
|-------|-----------------|
| `security-audit` | PASS, FIX, FAIL |
| `security-fix` | PASS, FIX, FAIL |
| `generic-fix` | PASS, FIX, FAIL |
| `validation-review` | PASS, FAIL |
| `test-coverage` | PASS, FIX, FAIL, SKIP |
| `plan-mode` | PASS, FAIL |

**Result Mappings** (defined per-agent in `config/agents.json`):
| Result | Status | Exit Code | Default Jump |
|--------|--------|-----------|--------------|
| `PASS` | success | 0 | next |
| `FAIL` | failure | 10 | abort |
| `FIX` | partial | 0 | prev |
| `SKIP` | success | 0 | next |

Each agent defines its own `result_mappings` in `config/agents.json`. Fallback mappings are in `defaults.result_mappings`. Pipeline-level overrides are also supported.

### Environment Variables for Config Override
Pattern: `WIGGUM_{AGENT_NAME}_MAX_TURNS` (uppercase, underscores)
- `WIGGUM_SECURITY_AUDIT_MAX_TURNS`
- `WIGGUM_TEST_COVERAGE_MAX_ITERATIONS`
