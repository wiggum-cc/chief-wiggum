# Chief Wiggum

**Chief Wiggum** is an agentic task runner and worker manager that enables autonomous coding agents to work on your projects in parallel. It uses a Kanban-driven approach to manage tasks and executes them using isolated workers.

It is built around the **[Ralph Wiggum](https://awesomeclaude.ai/ralph-wiggum)** pattern, designing agents that are "simple, happy, and do one thing at a time."

> "Bake him away, toys."

## Overview

Chief Wiggum monitors a `.ralph/kanban.md` file in your project. For every incomplete task, it spawns an isolated worker. Each worker:

1.  Creates a dedicated **git worktree** to ensure complete isolation from your main working directory and other workers.
2.  Generates a **PRD (Product Requirement Document)** specific to that task.
3.  Enters the **Ralph Loop**, autonomously driving **Claude Code** to execute specific tasks until completion.
4.  Merges results back and updates the Kanban board.

## Prerequisites

- **Linux/macOS** (Bash environment)
- **Git**
- **Claude Code** (`claude` CLI installed and authenticated)

## Installation & Usage

Chief Wiggum can be installed globally to your system path or run directly from the repository.

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

You can run Chief Wiggum directly from this repository by setting `CHIEF_HOME` to the current directory:

```bash
export CHIEF_HOME=$(pwd)
export PATH="$CHIEF_HOME/bin:$PATH"
```

## Quick Start

### 1. Initialize a Project

Navigate to any git repository where you want to use Chief Wiggum and initialize the configuration:

```bash
cd /path/to/your/project
chief init
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

### 3. Start Workers

Run `chief run` to spawn workers for incomplete tasks:

```bash
chief run
```

Chief will:
- Assign pending tasks to workers (up to 4 concurrent workers by default)
- Mark assigned tasks as `[=]` in-progress
- Monitor workers and spawn new ones as workers finish
- Wait until all tasks are complete
- Display progress updates

To change the maximum concurrent workers:

```bash
chief run --max-workers 8
```

### 4. Monitor & Manage

Check the status of active workers:

```bash
chief-status
```

Stop all workers:

```bash
chief-stop
```

## Architecture

- **`chief`**: Main process that parses the Kanban board and orchestrates workers.
- **Workers**: Isolated processes running in temporary git worktrees (`.ralph/workers/`).
- **Ralph Loop**: The core execution loop (`lib/ralph-loop.sh`) that prompts Claude Code to read the PRD, execute work, and verify results.
- **Skills**: Custom skills provided to the agent to help it report progress and complete tasks.

## Directory Structure

When running, Chief Wiggum creates:

```text
.ralph/
├── kanban.md       # The source of truth for tasks
├── workers/        # Temporary worktrees for active agents
├── results/        # Artifacts from completed tasks
└── logs/           # Worker logs
```
