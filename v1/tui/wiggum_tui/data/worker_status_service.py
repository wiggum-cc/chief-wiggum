"""Shared worker status service with TTL-based caching.

This service caches scan_workers() results to avoid redundant subprocess
calls when multiple panels query worker status within a short time window.
"""

import time
from pathlib import Path

from .worker_scanner import scan_workers
from .models import Worker, WorkerStatus


class WorkerStatusService:
    """Shared service for worker status with TTL-based caching.

    This service caches the results of scan_workers() to avoid redundant
    subprocess calls when multiple UI panels need worker data within
    a short time window.
    """

    def __init__(self, ralph_dir: Path, cache_ttl: float = 0.5) -> None:
        """Initialize the service.

        Args:
            ralph_dir: Path to .ralph directory.
            cache_ttl: Cache time-to-live in seconds. Results older than
                this will trigger a refresh on next access.
        """
        self.ralph_dir = ralph_dir
        self.cache_ttl = cache_ttl
        self._workers: list[Worker] = []
        self._running_tasks: dict[str, tuple[bool, int | None]] = {}
        self._last_scan: float = 0.0

    def _maybe_refresh(self) -> None:
        """Refresh cache if TTL has expired."""
        now = time.monotonic()
        if now - self._last_scan < self.cache_ttl:
            return

        self._workers = scan_workers(self.ralph_dir)
        self._last_scan = now

        # Build running tasks map
        self._running_tasks.clear()
        for worker in self._workers:
            if worker.status == WorkerStatus.RUNNING:
                # Only track most recent worker per task
                if worker.task_id not in self._running_tasks:
                    self._running_tasks[worker.task_id] = (True, worker.timestamp)

    def get_workers(self) -> list[Worker]:
        """Get all workers.

        Returns:
            List of Worker objects, sorted by timestamp (newest first).
        """
        self._maybe_refresh()
        return self._workers

    def get_task_running_status(self, task_ids: list[str]) -> dict[str, tuple[bool, int | None]]:
        """Get running status for multiple tasks.

        Args:
            task_ids: List of task IDs to check.

        Returns:
            Dictionary mapping task_id to (is_running, start_timestamp).
            start_timestamp is the agent.pid mtime (current agent start time) when running.
        """
        self._maybe_refresh()

        result: dict[str, tuple[bool, int | None]] = {}
        for task_id in task_ids:
            result[task_id] = self._running_tasks.get(task_id, (False, None))
        return result

    def invalidate(self) -> None:
        """Force cache invalidation on next access."""
        self._last_scan = 0.0
