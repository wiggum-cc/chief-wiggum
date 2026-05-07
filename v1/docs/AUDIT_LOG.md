# Audit Log Documentation

## Overview

Chief Wiggum maintains a comprehensive audit trail of all task assignments and worker lifecycle events in `.ralph/logs/audit.log`. This provides security accountability and helps track who ran what task and when.

## Location

The audit log is stored at:
```
.ralph/logs/audit.log
```

## Format

Each audit log entry follows this format:
```
[TIMESTAMP] EVENT_TYPE | KEY=VALUE pairs
```

### Fields

- **timestamp**: ISO 8601 formatted timestamp (e.g., `2025-01-18T12:00:00+00:00`)
- **event**: Event type (see Event Types below)
- **task_id**: Task identifier (e.g., `TASK-001`)
- **worker_id**: Worker identifier (e.g., `worker-TASK-001-12345`)
- **git_user**: Git user from git config in format `name <email>`
- **system_user**: System user who invoked the command in format `user@hostname`
- **pid**: Process ID of the worker
- **status**: Task completion status (`COMPLETE`, `FAILED`, or `TIMEOUT`)

## Event Types

### TASK_ASSIGNED
Logged when a task is assigned to a worker.

**Fields:**
- `task_id`: The task being assigned
- `worker_id`: The worker receiving the task
- `git_user`: Git user identity
- `system_user`: System user identity
- `pid`: Worker process ID

**Example:**
```
[2025-01-18T12:00:00+00:00] TASK_ASSIGNED | task_id=TASK-001 | worker_id=worker-TASK-001-12345 | git_user=John Doe <john@example.com> | system_user=john@localhost | pid=12345
```

### WORKER_START
Logged when a worker process starts.

**Fields:**
- `task_id`: The task being worked on
- `worker_id`: The worker identifier
- `git_user`: Git user identity
- `system_user`: System user identity
- `pid`: Worker process ID

**Example:**
```
[2025-01-18T12:00:05+00:00] WORKER_START | task_id=TASK-001 | worker_id=worker-TASK-001-12345 | git_user=John Doe <john@example.com> | system_user=john@localhost | pid=12345
```

### WORKER_CLEANUP
Logged when a worker begins its cleanup phase.

**Fields:**
- `task_id`: The task being cleaned up
- `worker_id`: The worker identifier
- `git_user`: Git user identity
- `system_user`: System user identity
- `pid`: Worker process ID

**Example:**
```
[2025-01-18T12:15:00+00:00] WORKER_CLEANUP | task_id=TASK-001 | worker_id=worker-TASK-001-12345 | git_user=John Doe <john@example.com> | system_user=john@localhost | pid=12345
```

### WORKER_COMPLETE
Logged when a worker completes successfully.

**Fields:**
- `task_id`: The completed task
- `worker_id`: The worker identifier
- `status`: `COMPLETE`
- `git_user`: Git user identity
- `system_user`: System user identity
- `pid`: Worker process ID

**Example:**
```
[2025-01-18T12:15:30+00:00] WORKER_COMPLETE | task_id=TASK-001 | worker_id=worker-TASK-001-12345 | status=COMPLETE | git_user=John Doe <john@example.com> | system_user=john@localhost | pid=12345
```

### WORKER_FAILED
Logged when a worker fails or times out.

**Fields:**
- `task_id`: The failed task
- `worker_id`: The worker identifier
- `status`: `FAILED` or `TIMEOUT`
- `git_user`: Git user identity
- `system_user`: System user identity
- `pid`: Worker process ID

**Example:**
```
[2025-01-18T12:15:30+00:00] WORKER_FAILED | task_id=TASK-001 | worker_id=worker-TASK-001-12345 | status=FAILED | git_user=John Doe <john@example.com> | system_user=john@localhost | pid=12345
```

## User Identity Tracking

### Git User Information

Chief Wiggum captures git user information from the git configuration:
```bash
git config user.name   # e.g., "John Doe"
git config user.email  # e.g., "john@example.com"
```

This is formatted as: `name <email>`

If git user information is not available, it will be logged as `unknown <unknown>`.

### System User Information

The system user who invoked the `wiggum run` command is captured as:
```
$USER@$(hostname)
```

For example: `john@localhost` or `jane@dev-server-01`

## Example Audit Trail

Here's a complete example of an audit trail for a task lifecycle:

```
[2025-01-18T10:00:00+00:00] TASK_ASSIGNED | task_id=TASK-001 | worker_id=worker-TASK-001-98765 | git_user=Alice Smith <alice@example.com> | system_user=alice@dev-laptop | pid=98765
[2025-01-18T10:00:01+00:00] WORKER_START | task_id=TASK-001 | worker_id=worker-TASK-001-98765 | git_user=Alice Smith <alice@example.com> | system_user=alice@dev-laptop | pid=98765
[2025-01-18T10:12:30+00:00] WORKER_CLEANUP | task_id=TASK-001 | worker_id=worker-TASK-001-98765 | git_user=Alice Smith <alice@example.com> | system_user=alice@dev-laptop | pid=98765
[2025-01-18T10:12:45+00:00] WORKER_COMPLETE | task_id=TASK-001 | worker_id=worker-TASK-001-98765 | status=COMPLETE | git_user=Alice Smith <alice@example.com> | system_user=alice@dev-laptop | pid=98765
```

## Querying the Audit Log

### Find all tasks assigned to a specific user
```bash
grep "git_user=John Doe" .ralph/logs/audit.log
```

### Find all failed tasks
```bash
grep "WORKER_FAILED" .ralph/logs/audit.log
```

### Find all events for a specific task
```bash
grep "task_id=TASK-001" .ralph/logs/audit.log
```

### Find all events from a specific system user
```bash
grep "system_user=alice@dev-laptop" .ralph/logs/audit.log
```

### Get a timeline of all worker starts today
```bash
grep "WORKER_START" .ralph/logs/audit.log | grep "$(date +%Y-%m-%d)"
```

## Security Considerations

1. **Immutable Log**: The audit log is append-only. Entries should never be deleted or modified.

2. **User Attribution**: Both git and system user information are captured to provide dual attribution:
   - Git user: Who is credited for the commits
   - System user: Who actually ran the command

3. **Timestamp Integrity**: All timestamps use ISO 8601 format with timezone information for unambiguous time tracking.

4. **Process Tracking**: PIDs allow correlation with system logs and process monitoring.

## Integration

The audit logging is automatically enabled when using Chief Wiggum. No configuration is required.

The audit log is implemented in `lib/audit-logger.sh` and integrated into:
- `bin/wiggum-run` - Logs task assignments
- `lib/worker.sh` - Logs worker lifecycle events
