"""File watcher for real-time updates."""

import asyncio
from pathlib import Path
from typing import Callable, Awaitable


class RalphWatcher:
    """Watch .ralph directory for changes and notify callbacks."""

    def __init__(self, ralph_dir: Path, poll_interval: float = 2.0):
        """Initialize watcher.

        Args:
            ralph_dir: Path to .ralph directory.
            poll_interval: Seconds between polls (default 2.0).
        """
        self.ralph_dir = ralph_dir
        self.poll_interval = poll_interval
        self._running = False
        self._task: asyncio.Task | None = None

        # Track file modification times
        self._mtimes: dict[str, float] = {}

        # Callbacks by category
        self._callbacks: dict[str, list[Callable[[], Awaitable[None]]]] = {
            "kanban": [],
            "workers": [],
            "logs": [],
            "metrics": [],
        }

    def on_kanban_change(self, callback: Callable[[], Awaitable[None]]) -> None:
        """Register callback for kanban.md changes."""
        self._callbacks["kanban"].append(callback)

    def on_workers_change(self, callback: Callable[[], Awaitable[None]]) -> None:
        """Register callback for workers directory changes."""
        self._callbacks["workers"].append(callback)

    def on_logs_change(self, callback: Callable[[], Awaitable[None]]) -> None:
        """Register callback for log file changes."""
        self._callbacks["logs"].append(callback)

    def on_metrics_change(self, callback: Callable[[], Awaitable[None]]) -> None:
        """Register callback for metrics.json changes."""
        self._callbacks["metrics"].append(callback)

    def _get_mtime(self, path: Path) -> float:
        """Get modification time of a file, 0 if not exists."""
        try:
            return path.stat().st_mtime
        except OSError:
            return 0

    def _get_dir_mtime(self, path: Path) -> float:
        """Get latest modification time in a directory."""
        if not path.is_dir():
            return 0
        try:
            latest = 0
            for item in path.iterdir():
                mtime = self._get_mtime(item)
                if mtime > latest:
                    latest = mtime
            return latest
        except OSError:
            return 0

    async def _notify(self, category: str) -> None:
        """Notify all callbacks for a category."""
        for callback in self._callbacks[category]:
            try:
                await callback()
            except Exception:
                pass  # Don't let callback errors stop the watcher

    async def _poll(self) -> None:
        """Poll for changes and notify callbacks."""
        while self._running:
            try:
                # Check kanban.md
                kanban_path = self.ralph_dir / "kanban.md"
                kanban_mtime = self._get_mtime(kanban_path)
                if kanban_mtime != self._mtimes.get("kanban", 0):
                    self._mtimes["kanban"] = kanban_mtime
                    await self._notify("kanban")

                # Check workers directory
                workers_path = self.ralph_dir / "workers"
                workers_mtime = self._get_dir_mtime(workers_path)
                if workers_mtime != self._mtimes.get("workers", 0):
                    self._mtimes["workers"] = workers_mtime
                    await self._notify("workers")

                # Check logs directory
                logs_path = self.ralph_dir / "logs"
                logs_mtime = self._get_dir_mtime(logs_path)
                if logs_mtime != self._mtimes.get("logs", 0):
                    self._mtimes["logs"] = logs_mtime
                    await self._notify("logs")

                # Check metrics.json
                metrics_path = self.ralph_dir / "metrics.json"
                metrics_mtime = self._get_mtime(metrics_path)
                if metrics_mtime != self._mtimes.get("metrics", 0):
                    self._mtimes["metrics"] = metrics_mtime
                    await self._notify("metrics")

            except Exception:
                pass  # Continue polling even on errors

            await asyncio.sleep(self.poll_interval)

    def start(self) -> None:
        """Start watching for changes."""
        if self._running:
            return
        self._running = True
        self._task = asyncio.create_task(self._poll())

    def stop(self) -> None:
        """Stop watching for changes."""
        self._running = False
        if self._task:
            self._task.cancel()
            self._task = None
