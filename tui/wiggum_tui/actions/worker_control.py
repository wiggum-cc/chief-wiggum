"""Worker control actions - stop, kill, verify."""

import os
import signal
from pathlib import Path


def stop_worker(pid: int) -> bool:
    """Send SIGTERM to gracefully stop a worker.

    Args:
        pid: Process ID of the worker.

    Returns:
        True if signal was sent, False if process not found.
    """
    try:
        os.kill(pid, signal.SIGTERM)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return False


def kill_worker(pid: int) -> bool:
    """Send SIGKILL to forcefully terminate a worker.

    Args:
        pid: Process ID of the worker.

    Returns:
        True if signal was sent, False if process not found.
    """
    try:
        os.kill(pid, signal.SIGKILL)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return False


def verify_worker_process(pid: int) -> bool:
    """Verify PID is actually a worker process.

    Args:
        pid: Process ID to verify.

    Returns:
        True if the process is a worker, False otherwise.
    """
    try:
        cmdline_path = Path(f"/proc/{pid}/cmdline")
        if cmdline_path.exists():
            cmdline = cmdline_path.read_text()
            # Agents run in bash subshells via run_agent()
            return "bash" in cmdline
        return False
    except (OSError, PermissionError):
        return False


def is_process_running(pid: int) -> bool:
    """Check if a process is running.

    Args:
        pid: Process ID to check.

    Returns:
        True if process exists, False otherwise.
    """
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        # Process exists but we can't signal it
        return True
