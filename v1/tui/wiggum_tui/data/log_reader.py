"""Log reader with parsing and tailing support."""

import json
import re
from pathlib import Path
from collections import deque
from .models import LogLine, LogLevel


# Pattern: [timestamp] LEVEL: message
LOG_PATTERN = re.compile(r"^\[([^\]]+)\]\s+(DEBUG|INFO|WARN|ERROR):\s*(.*)$")


def parse_log_line(line: str) -> LogLine:
    """Parse a single log line.

    Args:
        line: Raw log line string.

    Returns:
        Parsed LogLine object.
    """
    line = line.rstrip("\n\r")
    match = LOG_PATTERN.match(line)

    if match:
        timestamp, level_str, message = match.groups()
        try:
            level = LogLevel[level_str]
        except KeyError:
            level = None
        return LogLine(
            raw=line,
            timestamp=timestamp,
            level=level,
            message=message,
        )

    # Non-matching line - treat as continuation or raw message
    return LogLine(raw=line, message=line)


def read_log(file_path: Path, max_lines: int = 500) -> list[LogLine]:
    """Read log file and parse lines.

    Args:
        file_path: Path to log file.
        max_lines: Maximum number of lines to return (from end of file).

    Returns:
        List of parsed LogLine objects.
    """
    if not file_path.exists():
        return []

    try:
        content = file_path.read_text()
        lines = content.split("\n")

        # Take last max_lines
        if len(lines) > max_lines:
            lines = lines[-max_lines:]

        return [parse_log_line(line) for line in lines if line.strip()]
    except OSError:
        return []


def tail_log(file_path: Path, max_lines: int = 100) -> list[LogLine]:
    """Read last N lines of a log file efficiently.

    Args:
        file_path: Path to log file.
        max_lines: Number of lines to read from end.

    Returns:
        List of parsed LogLine objects.
    """
    if not file_path.exists():
        return []

    try:
        # Use deque to efficiently keep last N lines
        with open(file_path, "r") as f:
            lines = deque(f, maxlen=max_lines)
        return [parse_log_line(line) for line in lines if line.strip()]
    except OSError:
        return []


def filter_by_level(
    logs: list[LogLine], min_level: LogLevel | None = None
) -> list[LogLine]:
    """Filter logs by minimum level.

    Args:
        logs: List of log lines.
        min_level: Minimum level to include (None = all).

    Returns:
        Filtered list of log lines.
    """
    if min_level is None:
        return logs

    level_order = {
        LogLevel.DEBUG: 0,
        LogLevel.INFO: 1,
        LogLevel.WARN: 2,
        LogLevel.ERROR: 3,
    }
    min_order = level_order.get(min_level, 0)

    return [
        log
        for log in logs
        if log.level is None or level_order.get(log.level, 0) >= min_order
    ]


def search_logs(logs: list[LogLine], query: str) -> list[LogLine]:
    """Search logs for a query string (case-insensitive).

    Args:
        logs: List of log lines.
        query: Search query.

    Returns:
        List of matching log lines.
    """
    query_lower = query.lower()
    return [log for log in logs if query_lower in log.raw.lower()]


class LogTailer:
    """Efficient log file tailer that tracks position."""

    def __init__(self, file_path: Path, max_buffer: int = 1000):
        """Initialize tailer.

        Args:
            file_path: Path to log file.
            max_buffer: Maximum lines to keep in buffer.
        """
        self.file_path = file_path
        self.max_buffer = max_buffer
        self.position = 0
        self.buffer: deque[LogLine] = deque(maxlen=max_buffer)
        self._initialized = False

    def get_new_lines(self) -> list[LogLine]:
        """Get new lines since last read.

        Returns:
            List of new log lines.
        """
        if not self.file_path.exists():
            return []

        try:
            with open(self.file_path, "r") as f:
                # Handle file truncation (file got smaller)
                f.seek(0, 2)  # Go to end
                file_size = f.tell()

                if file_size < self.position:
                    # File was truncated, start over
                    self.position = 0
                    self.buffer.clear()

                if not self._initialized:
                    # On first read, read last max_buffer lines
                    f.seek(0)
                    lines = f.readlines()
                    if len(lines) > self.max_buffer:
                        lines = lines[-self.max_buffer :]
                    new_logs = [parse_log_line(line) for line in lines if line.strip()]
                    self.buffer.extend(new_logs)
                    self.position = file_size
                    self._initialized = True
                    return list(self.buffer)

                # Read from last position
                f.seek(self.position)
                new_lines = f.readlines()
                self.position = f.tell()

                new_logs = [parse_log_line(line) for line in new_lines if line.strip()]
                self.buffer.extend(new_logs)
                return new_logs

        except OSError:
            return []

    def get_all_lines(self) -> list[LogLine]:
        """Get all buffered lines.

        Returns:
            List of all buffered log lines.
        """
        return list(self.buffer)


def parse_activity_log(path: Path, max_lines: int = 500) -> list[LogLine]:
    """Parse a NDJSON activity log file into LogLine objects.

    Each line is a JSON object with at least an "event" field.
    Formatted as: [timestamp] event: task_id details

    Args:
        path: Path to activity.jsonl file.
        max_lines: Maximum number of lines to return.

    Returns:
        List of parsed LogLine objects.
    """
    if not path.exists():
        return []

    lines: list[LogLine] = []
    try:
        with open(path, "r") as f:
            raw_lines = deque(f, maxlen=max_lines)

        for raw_line in raw_lines:
            raw_line = raw_line.strip()
            if not raw_line:
                continue
            try:
                data = json.loads(raw_line)
                event = data.get("event", "unknown")
                task_id = data.get("task_id", "")
                timestamp = data.get("timestamp", "")

                # Build a human-readable message
                details_parts = []
                if task_id:
                    details_parts.append(task_id)
                for key in ("agent", "step_id", "result", "message", "status"):
                    if key in data:
                        details_parts.append(f"{key}={data[key]}")
                details = " ".join(details_parts)

                # Map event types to log levels
                level = LogLevel.INFO
                if "error" in event.lower() or "fail" in event.lower():
                    level = LogLevel.ERROR
                elif "warn" in event.lower():
                    level = LogLevel.WARN
                elif "debug" in event.lower():
                    level = LogLevel.DEBUG

                lines.append(LogLine(
                    raw=raw_line,
                    timestamp=str(timestamp) if timestamp else None,
                    level=level,
                    message=f"{event}: {details}",
                ))
            except json.JSONDecodeError:
                lines.append(LogLine(raw=raw_line, message=raw_line))
    except OSError:
        pass

    return lines


def discover_worker_log_sources(ralph_dir: Path) -> list[tuple[str, str, Path]]:
    """Discover all log sources from worker directories.

    Returns:
        List of (task_id_with_status, worker_dir_name, log_path) tuples,
        sorted by worker timestamp (newest first).
    """
    workers_dir = ralph_dir / "workers"
    if not workers_dir.is_dir():
        return []

    sources: list[tuple[str, str, Path, int]] = []

    for entry in sorted(workers_dir.iterdir(), reverse=True):
        if not entry.name.startswith("worker-") or not entry.is_dir():
            continue

        # Extract task_id and timestamp from dir name
        from .worker_scanner import WORKER_PATTERN
        match = WORKER_PATTERN.match(entry.name)
        if not match:
            continue

        task_id, ts_str = match.groups()
        try:
            timestamp = int(ts_str)
        except ValueError:
            timestamp = 0

        # Determine status from agent.pid presence
        has_pid = (entry / "agent.pid").exists()
        status = "running" if has_pid else "stopped"

        # Check for PRD status
        prd_path = entry / "prd.md"
        if not has_pid and prd_path.exists():
            try:
                content = prd_path.read_text()
                if "- [*]" in content:
                    status = "failed"
                elif "- [ ]" not in content:
                    status = "completed"
            except OSError:
                pass

        label = f"{task_id} ({status})"

        # Add worker.log
        worker_log = entry / "worker.log"
        if worker_log.exists():
            sources.append((label, entry.name, worker_log, timestamp))

        # Add nested log directories
        logs_dir = entry / "logs"
        if logs_dir.is_dir():
            for log_subdir in sorted(logs_dir.iterdir()):
                if log_subdir.is_dir():
                    for log_file in sorted(log_subdir.glob("*.log")):
                        rel = f"{log_subdir.name}/{log_file.name}"
                        sources.append((label, rel, log_file, timestamp))

    # Already sorted by directory order (newest first)
    return [(s[0], s[1], s[2]) for s in sources]
