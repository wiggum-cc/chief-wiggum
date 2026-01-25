# Architecture

This document describes the internal architecture of Chief Wiggum for developers who want to understand, extend, or debug the system.

## Directory Structure

```
chief-wiggum/
├── bin/                    # CLI entry points
│   ├── wiggum              # Main orchestrator
│   ├── wiggum-start        # Worker spawner
│   ├── wiggum-monitor      # Log viewer
│   ├── wiggum-review       # PR management
│   ├── wiggum-validate     # Kanban validator
│   └── wiggum-clean        # Cleanup utility
├── lib/
│   ├── agents/             # Agent implementations
│   │   ├── system/         # Core system agents
│   │   ├── engineering/    # Code quality agents
│   │   └── product/        # Product/docs agents
│   ├── claude/             # Claude Code invocation
│   ├── core/               # Shared utilities
│   ├── git/                # Git operations
│   ├── pipeline/           # Pipeline engine
│   ├── tasks/              # Kanban parsing
│   ├── utils/              # Logging, metrics
│   └── worker/             # Worker lifecycle
├── config/
│   ├── pipeline.json       # Default pipeline
│   ├── agents.json         # Agent registry
│   └── schemas/            # JSON schemas
├── tests/                  # Test suite
└── docs/                   # Documentation
```

## Component Overview

### Orchestrator (`bin/wiggum`)

The main entry point that:
1. Parses the Kanban board (`.ralph/kanban.md`)
2. Identifies pending tasks
3. Spawns workers up to the concurrency limit
4. Monitors worker completion
5. Updates task status in Kanban

### Workers

Each worker is an isolated process that:
1. Runs in a dedicated git worktree (`.ralph/workers/worker-TASK-XXX-<timestamp>/`)
2. Executes a pipeline of agents
3. Creates a PR on completion
4. Reports status back to orchestrator

Workers are fully isolated—they share no state and can run in parallel.

### Pipeline Engine

The pipeline (`lib/pipeline/`) is a jump-based state machine that sequences agent execution.

```
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│ planning │───►│execution │───►│  audit   │───►│   test   │───►...
└──────────┘    └──────────┘    └──────────┘    └──────────┘
                     │               │
                     │ FAIL          │ FIX
                     ▼               ▼
                  [abort]       [audit-fix]
                                     │
                                     │ re-run parent
                                     ▼
                                 [audit]
```

Key concepts:
- **Steps**: Ordered array of agent invocations
- **on_result**: Per-result handlers (jump or inline agent)
- **max**: Visit limit to prevent infinite loops
- **on_max**: Fallback target when max exceeded (default: `next`)

See [PIPELINE-SCHEMA.md](PIPELINE-SCHEMA.md) for the full specification.

### Agents

Agents are bash scripts that implement a standard interface:

```bash
agent_run(worker_dir, project_dir, workspace, output_dir)
```

Agents invoke Claude Code to perform work. Each agent focuses on a single responsibility:

| Agent | Purpose |
|-------|---------|
| `system.task-executor` | Main implementation work via Ralph Loop |
| `system.task-summarizer` | Generate completion summary |
| `engineering.security-audit` | Security review (readonly) |
| `engineering.security-fix` | Fix security issues |
| `engineering.test-coverage` | Run and fix tests |
| `engineering.validation-review` | Final validation against PRD |
| `product.plan-mode` | Interactive planning (optional) |
| `product.documentation-writer` | Update docs |

See [AGENT_DEV_GUIDE.md](AGENT_DEV_GUIDE.md) for writing custom agents.

## Claude Invocation Patterns

Agents invoke Claude Code through three patterns in `lib/claude/`:

### 1. Single Execution (`run-claude-once.sh`)

One-shot prompts with no session continuity:

```bash
run_agent_once "$workspace" "$system_prompt" "$user_prompt" "$output_file" "$max_turns"
```

Used for: validation, summarization, simple tasks.

### 2. Ralph Loop (`run-claude-ralph-loop.sh`)

Iterative work with context preservation between iterations:

```bash
run_ralph_loop "$workspace" "$system_prompt" \
    "_user_prompt_callback" \
    "_completion_check_callback" \
    "$max_iterations" "$max_turns" "$output_dir"
```

Each iteration:
1. Check completion callback
2. Generate prompt via callback
3. Claude executes with turn limit
4. Resume session to generate summary
5. Summary becomes context for next iteration

This prevents context bloat by starting fresh sessions while carrying forward summaries.

### 3. Supervised Ralph Loop (`run-claude-ralph-loop-supervised.sh`)

Ralph Loop with periodic intervention checkpoints:

```bash
run_ralph_loop_supervised "$workspace" "$system_prompt" \
    "_user_prompt_callback" \
    "_completion_check_callback" \
    "$max_iterations" "$max_turns" "$output_dir" \
    "$supervisor_interval" "$supervisor_agent"
```

Every N iterations, a supervisor agent reviews progress and can redirect work.

## Data Flow

### Task Lifecycle

```
┌─────────────────────────────────────────────────────────────────┐
│                        ORCHESTRATOR                              │
│  .ralph/kanban.md ──► Task Parser ──► Worker Spawner            │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                          WORKER                                  │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │ Git Worktree: .ralph/workers/worker-TASK-XXX-<ts>/      │    │
│  │   ├── workspace/     # Cloned project                    │    │
│  │   ├── prd.md         # Generated requirements            │    │
│  │   ├── output/        # Agent outputs                     │    │
│  │   └── activity.jsonl # Event log                         │    │
│  └─────────────────────────────────────────────────────────┘    │
│                              │                                   │
│                              ▼                                   │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    PIPELINE                              │    │
│  │  planning ─► execution ─► summary ─► audit ─► test ─►...│    │
│  └─────────────────────────────────────────────────────────┘    │
│                              │                                   │
│                              ▼                                   │
│                         Create PR                                │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                        ORCHESTRATOR                              │
│              Update kanban: [ ] ──► [=] ──► [x]                 │
└─────────────────────────────────────────────────────────────────┘
```

### Agent Execution

```
┌─────────────────────────────────────────────────────────────────┐
│                         AGENT                                    │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    RALPH LOOP                            │    │
│  │  ┌──────────┐    ┌──────────┐    ┌──────────┐           │    │
│  │  │ Iter 0   │───►│ Iter 1   │───►│ Iter N   │           │    │
│  │  │ Work     │    │ Work     │    │ Work     │           │    │
│  │  │ Summary  │    │ Summary  │    │ Summary  │           │    │
│  │  └──────────┘    └──────────┘    └──────────┘           │    │
│  │       │               │               │                  │    │
│  │       ▼               ▼               ▼                  │    │
│  │   [context]──────►[context]──────►[context]              │    │
│  └─────────────────────────────────────────────────────────┘    │
│                              │                                   │
│                              ▼                                   │
│                    Gate Result: PASS/FAIL/FIX                    │
└─────────────────────────────────────────────────────────────────┘
```

## File Conventions

### Worker Directory

```
.ralph/workers/worker-TASK-001-1234567890/
├── workspace/              # Git worktree (project clone)
├── prd.md                  # Product requirements document
├── output/                 # Agent outputs
│   ├── execution/          # Per-agent output directories
│   ├── audit/
│   └── ...
├── step-config.json        # Current step configuration
├── activity.jsonl          # Event log (NDJSON)
├── agent.pid               # Running agent PID
└── gate_result             # Last agent result (PASS/FAIL/FIX/STOP)
```

### Activity Log Format

Events are logged to `activity.jsonl` in NDJSON format:

```json
{"ts":"2024-01-15T10:30:00Z","event":"step.started","step":"execution","agent":"system.task-executor"}
{"ts":"2024-01-15T10:35:00Z","event":"step.completed","step":"execution","result":"PASS"}
```

## Configuration

### Pipeline Configuration

`config/pipeline.json` defines the agent sequence:

```json
{
  "name": "default",
  "steps": [
    {"id": "execution", "agent": "system.task-executor", "max": 3},
    {"id": "audit", "agent": "engineering.security-audit", "readonly": true}
  ]
}
```

Override per-project in `.ralph/pipeline.json` or per-task in `.ralph/pipelines/<task-id>.json`.

### Agent Registry

`config/agents.json` maps agent names to implementations:

```json
{
  "system.task-executor": "lib/agents/system/task-executor.sh",
  "engineering.security-audit": "lib/agents/engineering/security-audit.sh"
}
```

## Key Libraries

| Library | Purpose |
|---------|---------|
| `lib/core/logger.sh` | Structured logging with levels |
| `lib/core/exit-codes.sh` | Standardized exit codes |
| `lib/core/file-lock.sh` | File-based locking |
| `lib/pipeline/pipeline-loader.sh` | Load and validate pipeline config |
| `lib/pipeline/pipeline-runner.sh` | Execute pipeline state machine |
| `lib/worker/agent-registry.sh` | Resolve agent names to scripts |
| `lib/worker/agent-runner.sh` | Agent lifecycle management |
| `lib/claude/run-claude-ralph-loop.sh` | Iterative Claude execution |
| `lib/git/worktree-helpers.sh` | Git worktree operations |
| `lib/tasks/task-parser.sh` | Kanban markdown parsing |
| `lib/utils/activity-log.sh` | Event logging |

## Exit Codes

Defined in `lib/core/exit-codes.sh`:

| Code | Meaning |
|------|---------|
| 0 | Success |
| 1 | General error |
| 2 | Invalid arguments |
| 3 | Configuration error |
| 4 | Git error |
| 5 | Claude error |
| 10 | Agent FAIL result |
| 11 | Agent STOP result |
| 12 | Max iterations exceeded |

## Testing

Run the test suite:

```bash
./tests/test-runner.sh           # All tests
bash tests/test_pipeline_*.sh    # Pipeline tests only
```

Tests use a lightweight assertion framework defined in each test file.

## Debugging

### Inspect Command

The `wiggum inspect` command provides debugging utilities:

```bash
# Inspect a worker's state
wiggum inspect worker TASK-001

# Show pipeline configuration
wiggum inspect pipeline
wiggum inspect pipeline config/pipeline.json

# List available agents with configs
wiggum inspect agents

# View activity log (global or per-worker)
wiggum inspect activity
wiggum inspect activity TASK-001

# Show current pipeline step for a worker
wiggum inspect step TASK-001
```

### Verbose Logging

```bash
WIGGUM_LOG_LEVEL=debug wiggum run
```

### Manual Inspection

```bash
# List active workers
ls -la .ralph/workers/

# View worker logs
tail -f .ralph/workers/worker-TASK-001-*/output/*/claude.log

# Check activity log
cat .ralph/workers/worker-TASK-001-*/activity.jsonl | jq .
```

### Manual Pipeline Execution

```bash
# Load pipeline functions
source lib/pipeline/pipeline-loader.sh
source lib/pipeline/pipeline-runner.sh

# Load a pipeline
pipeline_load config/pipeline.json

# Inspect loaded state
echo "Steps: $(pipeline_step_count)"
echo "Step 0: $(pipeline_get_id 0) -> $(pipeline_get_agent 0)"
```
