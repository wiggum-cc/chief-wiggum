---
name: complete-task
description: Mark task complete in kanban
---

# Complete Task

This skill is called automatically by the worker cleanup process.

## What it does

1. Copies workspace changes to `.ralph/results/TASK-ID/`
2. Updates kanban.md - marks task checkbox as `[x]`
3. Removes git worktree
4. Worker process exits

## Usage

This is automatically invoked by `lib/worker.sh` when a worker completes its PRD tasks. You don't need to call this manually.

## Implementation

The actual implementation is in the `cleanup_worker()` function in `lib/worker.sh`:

```bash
# Mark task complete in kanban
sed -i "s/- \[ \] \*\*\[$TASK_ID\]\*\*/- [x] **[$TASK_ID]**/" "$PROJECT_DIR/.ralph/kanban.md"
```
