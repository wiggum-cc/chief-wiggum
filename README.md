# Chief Wiggum

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Bash](https://img.shields.io/badge/Language-Bash-blue)](https://www.gnu.org/software/bash/)
[![Ralph Wiggum](https://img.shields.io/badge/CI-passing-green)](https://github.com/0kenx/chief-wiggum)

**Chief Wiggum** is an agentic task runner that helps your computer do things while you're sleeping! It uses the **[Ralph Wiggum](https://awesomeclaude.ai/ralph-wiggum)** way of doing things: "simple, happy, and do one thing at a time."

![Chief Wiggum](docs/chief_wiggum.jpeg)

> "Bake him away, toys."

## Overview

Chief Wiggum monitors a `.ralph/kanban.md` file in your project. For every incomplete task, it spawns an isolated worker. Each worker:

1.  Creates a dedicated **git worktree** to ensure complete isolation from your main working directory and other workers.
2.  Generates a **PRD (Product Requirement Document)** specific to that task.
3.  Enters the **Ralph Loop**, autonomously driving **Claude Code** to execute specific tasks until completion.
4.  Merges results back via Pull Requests and updates the Kanban board.

## Prerequisites

- **Linux/macOS** (Bash environment)
- **Git**
- **Claude Code** (`claude` CLI installed and authenticated)
- **GitHub CLI** (`gh` installed and authenticated) - Required for PR management

## Installation & Usage

### Option 1: Global Installation

Run the installation script to set up Chief Wiggum in `~/.claude/chief-wiggum`:

```bash
./install.sh
```

Then, add the binary directory to your PATH:

```bash
export PATH="$HOME/.claude/chief-wiggum/bin:$PATH"
```

### Option 2: Run from Source

You can run Chief Wiggum directly from this repository by setting `WIGGUM_HOME` to the current directory:

```bash
export WIGGUM_HOME=$(pwd)
export PATH="$WIGGUM_HOME/bin:$PATH"
```

## Quick Start

### 1. Initialize a Project

Navigate to any git repository where you want to use Chief Wiggum and initialize the configuration:

```bash
cd /path/to/your/project
wiggum init
```

This creates a `.ralph/` directory containing a `kanban.md` file.

### 2. Define Tasks

Edit `.ralph/kanban.md` to add tasks to the **TASKS** section.

```markdown
## TASKS

- [ ] **[TASK-001]** Refactor Authentication
  - Description: Split auth logic into a separate service...
  - Priority: HIGH
```

Task statuses:
- `- [ ]` - Pending (not yet assigned)
- `- [=]` - In Progress (worker actively working on it)
- `- [x]` - Complete (worker finished successfully)
- `- [*]` - Failed (worker encountered an error)

### 3. Validate Tasks

Before running workers, ensure your Kanban board is correctly formatted:

```bash
wiggum validate
```

This checks for:
- Correct Task ID format (`TASK-001`)
- Required fields (Description, Priority)
- Unique Task IDs
- Valid dependency references
- Proper indentation

### 4. Start Workers

Run `wiggum run` to spawn workers for incomplete tasks:

```bash
wiggum run
```

Chief will:
- Assign pending tasks to workers (up to 4 concurrent workers by default)
- Mark assigned tasks as `[=]` in-progress
- Monitor workers and spawn new ones as workers finish
- Wait until all tasks are complete

To change the maximum concurrent workers:

```bash
wiggum run --max-workers 8
```

### 5. Monitor Progress

Watch the status of active workers in real-time:

```bash
# View combined logs from all workers
wiggum monitor

# View status summary table
wiggum monitor status

# View split pane with recent logs for each worker
wiggum monitor split
```

Check the overall system status:

```bash
wiggum status
```

### 6. Review and Merge

Workers create Pull Requests for completed tasks. Manage them with:

```bash
# List open worker PRs
wiggum review list

# View a specific PR
wiggum review view 123

# Merge a specific PR
wiggum review merge 123

# Merge all open worker PRs
wiggum review merge-all
```

## Advanced Commands

### Cleanup

If you need to remove worktrees and temporary files (e.g., after a crash or to free up space):

```bash
wiggum clean
```

This removes all worker worktrees and clears the `.ralph/workers/` directory.

## Architecture

- **`wiggum`**: Main orchestrator.
- **`wiggum-validate`**: Ensures your instructions (Kanban) are legible.
- **`wiggum-monitor`**: Keeps an eye on the boys (workers).
- **`wiggum-review`**: Paperwork processing (PR management).
- **Workers**: Isolated processes running in temporary git worktrees (`.ralph/workers/`).
- **Ralph Loop**: The core execution loop (`lib/ralph-loop.sh`) that prompts Claude Code to read the PRD, execute work, and verify results.

### Context Window Management

The Ralph Loop uses a **controlled context window** approach to prevent context bloat:

1. Each iteration starts a fresh Claude session with a unique session ID.
2. Sessions are limited to a configurable number of turns (default: 20).
3. When a session hits the turn limit:
   - The session is resumed with `--resume <session-id>`
   - Claude provides a summary of work completed
   - The summary is appended to the PRD as a changelog entry
4. The next iteration reads the updated PRD (with changelog) and continues with fresh context.

This ensures each session stays within ~10-15K tokens instead of growing unbounded.

## Directory Structure

When running, Chief Wiggum creates:

```text
.ralph/
├── kanban.md       # The source of truth for tasks
├── changelog.md    # Summary of all completed tasks
├── workers/        # Temporary worktrees for active agents
├── logs/           # Worker logs
└── metrics/        # Cost and performance tracking
```
