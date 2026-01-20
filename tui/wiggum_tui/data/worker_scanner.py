"""Worker scanner - ported from TypeScript."""

import re
import subprocess
from pathlib import Path
from .models import Worker, WorkerStatus


# Pattern: worker-TASK-XXX-TIMESTAMP
WORKER_PATTERN = re.compile(r"^worker-([A-Za-z]{2,8}-\d+)-(\d+)$")


def is_process_running(pid: int) -> bool:
    """Check if a process is running."""
    try:
        import os

        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def is_worker_process(pid: int) -> bool:
    """Check if PID is actually a worker process."""
    try:
        result = subprocess.run(
            ["ps", "-p", str(pid), "-o", "args="],
            capture_output=True,
            text=True,
            timeout=5,
        )
        # Agents run in bash subshells via run_agent()
        return "bash" in result.stdout
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return False


def is_orchestrator_process(pid: int) -> bool:
    """Check if PID is actually an orchestrator process."""
    try:
        result = subprocess.run(
            ["ps", "-p", str(pid), "-o", "args="],
            capture_output=True,
            text=True,
            timeout=5,
        )
        return "wiggum-run" in result.stdout
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return False


def get_prd_status(prd_path: Path) -> str:
    """Get status from PRD file content.

    Returns: 'complete', 'failed', or 'incomplete'
    """
    try:
        content = prd_path.read_text()
        if "- [*]" in content:
            return "failed"
        if "- [ ]" in content:
            return "incomplete"
        return "complete"
    except (OSError, FileNotFoundError):
        return "incomplete"


def scan_workers(ralph_dir: Path) -> list[Worker]:
    """Scan .ralph/workers directory for workers.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        List of Worker objects, sorted by timestamp (newest first).
    """
    workers_dir = ralph_dir / "workers"
    workers: list[Worker] = []

    if not workers_dir.is_dir():
        return workers

    for entry in workers_dir.iterdir():
        if not entry.name.startswith("worker-"):
            continue
        if not entry.is_dir():
            continue

        # Parse worker ID
        match = WORKER_PATTERN.match(entry.name)
        if not match:
            continue

        task_id, _ = match.groups()
        # Use actual directory modification time instead of name suffix
        try:
            timestamp = int(entry.stat().st_mtime)
        except OSError:
            timestamp = 0

        worker_dir = entry
        pid_path = worker_dir / "agent.pid"
        prd_path = worker_dir / "prd.md"
        log_path = worker_dir / "worker.log"
        workspace_path = worker_dir / "workspace"
        pr_url_path = worker_dir / "pr_url.txt"

        pid: int | None = None
        status = WorkerStatus.STOPPED

        # Check PID file
        if pid_path.exists():
            try:
                pid_content = pid_path.read_text().strip()
                parsed_pid = int(pid_content)
                pid = parsed_pid
                if is_process_running(parsed_pid) and is_worker_process(parsed_pid):
                    status = WorkerStatus.RUNNING
            except (ValueError, OSError):
                pass

        # If not running, check PRD status
        if status != WorkerStatus.RUNNING:
            prd_status = get_prd_status(prd_path)
            if prd_status == "complete":
                status = WorkerStatus.COMPLETED
            elif prd_status == "failed":
                status = WorkerStatus.FAILED

        # Check for PR URL
        pr_url: str | None = None
        if pr_url_path.exists():
            try:
                pr_url = pr_url_path.read_text().strip()
                if not pr_url:
                    pr_url = None
            except OSError:
                pass

        workers.append(
            Worker(
                id=entry.name,
                task_id=task_id,
                timestamp=timestamp,
                pid=pid,
                status=status,
                prd_path=str(prd_path),
                log_path=str(log_path),
                workspace_path=str(workspace_path),
                pr_url=pr_url,
            )
        )

    # Sort by timestamp descending (newest first)
    workers.sort(key=lambda w: w.timestamp, reverse=True)

    return workers


def get_orchestrator_status(ralph_dir: Path) -> tuple[bool, int | None]:
    """Get orchestrator status.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        Tuple of (running: bool, pid: int | None).
    """
    pid_path = ralph_dir / ".orchestrator.pid"

    if not pid_path.exists():
        return False, None

    try:
        pid_content = pid_path.read_text().strip()
        pid = int(pid_content)

        if is_process_running(pid) and is_orchestrator_process(pid):
            return True, pid
    except (ValueError, OSError):
        pass

    return False, None


def get_worker_counts(workers: list[Worker]) -> dict[str, int]:
    """Get count of workers in each status.

    Args:
        workers: List of workers.

    Returns:
        Dictionary with counts for each status.
    """
    counts = {
        "running": 0,
        "stopped": 0,
        "completed": 0,
        "failed": 0,
        "total": len(workers),
    }
    for worker in workers:
        counts[worker.status.value] += 1
    return counts
