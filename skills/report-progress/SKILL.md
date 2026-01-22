---
name: report-progress
description: Log worker progress to shared log
---

# Report Progress

Workers can use this to log progress updates to the shared log file.

## Usage

From within a worker's context:

```bash
echo "[$(date -Iseconds)] Worker $WORKER_ID: Completed step X" >> .ralph/logs/workers.log
```

## Automatic Progress Logging

Progress is automatically logged via the `on-task-progress.sh` hook whenever a worker modifies its PRD file.

## Viewing Progress

Users can view worker progress by:

```bash
# View all progress
cat .ralph/logs/workers.log

# Follow live updates
tail -f .ralph/logs/workers.log

# Check status
chief-status
```

## Log Format

Each log entry includes:
- ISO 8601 timestamp
- Worker ID
- Progress message

Example:
```
[2026-01-18T10:15:30Z] Worker worker-TASK-001-12345 made progress
```
