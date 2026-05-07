"""Metrics panel widget showing aggregate dashboard from worker logs."""

import json
from pathlib import Path
from dataclasses import dataclass, field
from textual.app import ComposeResult
from textual.containers import Horizontal
from textual.widgets import Static, DataTable
from textual.widget import Widget

from ..data.worker_scanner import scan_workers
from ..data.models import WorkerStatus
from ..data.status_reader import read_api_usage, read_memory_stats, read_worker_cost
from ..utils import format_relative_time


# Cache for aggregate metrics: ralph_dir_path -> (max_mtime, AggregateMetrics)
_metrics_cache: dict[str, tuple[float, "AggregateMetrics"]] = {}

# Cache for individual worker metrics: worker_dir_path -> (mtime, WorkerLogMetrics)
_worker_metrics_cache: dict[str, tuple[float, "WorkerLogMetrics"]] = {}


@dataclass
class WorkerLogMetrics:
    """Metrics parsed from a single worker's log file."""
    worker_id: str = ""
    task_id: str = ""
    status: str = ""
    num_turns: int = 0
    total_cost_usd: float = 0.0
    duration_ms: int = 0
    input_tokens: int = 0
    output_tokens: int = 0
    cache_creation_tokens: int = 0
    cache_read_tokens: int = 0


@dataclass
class AggregateMetrics:
    """Aggregated metrics from all workers."""
    total_workers: int = 0
    running_workers: int = 0
    completed_workers: int = 0
    failed_workers: int = 0
    merged_workers: int = 0
    total_turns: int = 0
    total_cost_usd: float = 0.0
    total_duration_ms: int = 0
    input_tokens: int = 0
    output_tokens: int = 0
    cache_creation_tokens: int = 0
    cache_read_tokens: int = 0
    worker_summaries: list[WorkerLogMetrics] = field(default_factory=list)


def get_workers_logs_max_mtime(ralph_dir: Path) -> float:
    """Get the maximum modification time of all worker logs directories.

    Uses directory mtime rather than individual files for efficiency.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        Maximum mtime of any logs directory, or 0 if none found.
    """
    workers_dir = ralph_dir / "workers"
    if not workers_dir.is_dir():
        return 0.0

    max_mtime = 0.0
    try:
        for worker_dir in workers_dir.iterdir():
            if not worker_dir.name.startswith("worker-") or not worker_dir.is_dir():
                continue
            logs_dir = worker_dir / "logs"
            if logs_dir.is_dir():
                try:
                    mtime = logs_dir.stat().st_mtime
                    if mtime > max_mtime:
                        max_mtime = mtime
                except OSError:
                    continue
    except OSError:
        pass
    return max_mtime


def get_worker_logs_mtime(worker_dir: Path) -> float:
    """Get the modification time of a worker's logs directory.

    Args:
        worker_dir: Path to worker directory.

    Returns:
        Mtime of the logs directory, or 0 if not found.
    """
    logs_dir = worker_dir / "logs"
    if logs_dir.is_dir():
        try:
            return logs_dir.stat().st_mtime
        except OSError:
            pass
    return 0.0


def parse_log_metrics(log_file: Path) -> list[dict]:
    """Parse a log file to find all JSON result entries."""
    results = []
    try:
        content = log_file.read_text()
        for line in content.split('\n'):
            line = line.strip()
            if not line:
                continue
            try:
                data = json.loads(line)
                if data.get("type") == "result":
                    results.append(data)
            except json.JSONDecodeError:
                continue
    except (OSError, FileNotFoundError):
        pass
    return results


def _parse_worker_logs(worker_dir: Path, worker_id: str, task_id: str, status: str) -> WorkerLogMetrics:
    """Parse logs for a single worker.

    Args:
        worker_dir: Path to worker directory.
        worker_id: Worker ID.
        task_id: Task ID.
        status: Worker status string.

    Returns:
        WorkerLogMetrics for this worker.
    """
    global _worker_metrics_cache

    cache_key = str(worker_dir.resolve())
    current_mtime = get_worker_logs_mtime(worker_dir)

    # Check per-worker cache
    if cache_key in _worker_metrics_cache:
        cached_mtime, cached_metrics = _worker_metrics_cache[cache_key]
        if cached_mtime >= current_mtime:
            # Update status in case it changed (running -> completed)
            cached_metrics.status = status
            return cached_metrics

    worker_metrics = WorkerLogMetrics(
        worker_id=worker_id,
        task_id=task_id,
        status=status,
    )

    logs_dir = worker_dir / "logs"
    if logs_dir.is_dir():
        # Use **/*.log to find logs in nested subdirectories
        for log_file in logs_dir.glob("**/*.log"):
            for result in parse_log_metrics(log_file):
                worker_metrics.num_turns += result.get("num_turns", 0)
                worker_metrics.total_cost_usd += result.get("total_cost_usd", 0.0)
                worker_metrics.duration_ms += result.get("duration_ms", 0)
                usage = result.get("usage", {})
                worker_metrics.input_tokens += usage.get("input_tokens", 0)
                worker_metrics.output_tokens += usage.get("output_tokens", 0)
                worker_metrics.cache_creation_tokens += usage.get("cache_creation_input_tokens", 0)
                worker_metrics.cache_read_tokens += usage.get("cache_read_input_tokens", 0)

    # Prefer cost-tracker.json for cost accuracy when available
    tracker_cost = read_worker_cost(worker_dir)
    if tracker_cost is not None:
        worker_metrics.total_cost_usd = tracker_cost

    # Cache the result
    _worker_metrics_cache[cache_key] = (current_mtime, worker_metrics)

    return worker_metrics


def aggregate_worker_metrics(ralph_dir: Path, use_cache: bool = True) -> AggregateMetrics:
    """Aggregate metrics from all worker logs.

    Args:
        ralph_dir: Path to .ralph directory.
        use_cache: If True, use cached result if logs haven't changed.

    Returns:
        AggregateMetrics with totals from all workers.
    """
    global _metrics_cache

    cache_key = str(ralph_dir.resolve())
    current_mtime = get_workers_logs_max_mtime(ralph_dir)

    # Check top-level cache
    if use_cache and cache_key in _metrics_cache:
        cached_mtime, cached_metrics = _metrics_cache[cache_key]
        if cached_mtime >= current_mtime:
            return cached_metrics

    metrics = AggregateMetrics()
    workers = scan_workers(ralph_dir)
    metrics.total_workers = len(workers)

    for worker in workers:
        if worker.status == WorkerStatus.RUNNING:
            metrics.running_workers += 1
        elif worker.status == WorkerStatus.COMPLETED:
            metrics.completed_workers += 1
        elif worker.status == WorkerStatus.FAILED:
            metrics.failed_workers += 1
        elif worker.status == WorkerStatus.MERGED:
            metrics.merged_workers += 1

        worker_dir = ralph_dir / "workers" / worker.id

        # Use per-worker caching for log parsing
        worker_metrics = _parse_worker_logs(
            worker_dir, worker.id, worker.task_id, worker.status.value
        )

        metrics.total_turns += worker_metrics.num_turns
        metrics.total_cost_usd += worker_metrics.total_cost_usd
        metrics.total_duration_ms += worker_metrics.duration_ms
        metrics.input_tokens += worker_metrics.input_tokens
        metrics.output_tokens += worker_metrics.output_tokens
        metrics.cache_creation_tokens += worker_metrics.cache_creation_tokens
        metrics.cache_read_tokens += worker_metrics.cache_read_tokens

        if worker_metrics.num_turns > 0 or worker_metrics.total_cost_usd > 0:
            metrics.worker_summaries.append(worker_metrics)

    metrics.worker_summaries.sort(key=lambda x: x.total_cost_usd, reverse=True)

    # Cache the result
    _metrics_cache[cache_key] = (current_mtime, metrics)

    return metrics


def parse_git_state_summary(ralph_dir: Path) -> dict[str, int]:
    """Scan worker git-state.json files and count by current_state.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        Dict mapping state name to count (e.g. {"merged": 5, "needs_fix": 2}).
    """
    counts: dict[str, int] = {}
    workers_dir = ralph_dir / "workers"
    if not workers_dir.is_dir():
        return counts

    for entry in workers_dir.iterdir():
        if not entry.name.startswith("worker-") or not entry.is_dir():
            continue
        git_state_path = entry / "git-state.json"
        if git_state_path.exists():
            try:
                data = json.loads(git_state_path.read_text())
                state = data.get("current_state", "unknown")
                counts[state] = counts.get(state, 0) + 1
            except (json.JSONDecodeError, OSError):
                continue

    return counts


def parse_pipeline_step_durations(ralph_dir: Path) -> dict[str, dict]:
    """Aggregate durations per pipeline step from worker result files.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        Dict mapping step_id to {"count": N, "total_ms": M, "avg_ms": A}.
    """
    steps: dict[str, dict] = {}
    workers_dir = ralph_dir / "workers"
    if not workers_dir.is_dir():
        return steps

    for entry in workers_dir.iterdir():
        if not entry.name.startswith("worker-") or not entry.is_dir():
            continue

        output_dir = entry / "output"
        if not output_dir.is_dir():
            continue

        for step_dir in output_dir.iterdir():
            if not step_dir.is_dir():
                continue
            step_id = step_dir.name

            # Look for result files with duration info
            for result_file in step_dir.glob("*.json"):
                try:
                    data = json.loads(result_file.read_text())
                    duration = data.get("duration_ms", 0)
                    if duration > 0:
                        if step_id not in steps:
                            steps[step_id] = {"count": 0, "total_ms": 0}
                        steps[step_id]["count"] += 1
                        steps[step_id]["total_ms"] += duration
                except (json.JSONDecodeError, OSError):
                    continue

    # Compute averages
    for step_id, info in steps.items():
        if info["count"] > 0:
            info["avg_ms"] = info["total_ms"] // info["count"]
        else:
            info["avg_ms"] = 0

    return steps


def parse_service_metrics(ralph_dir: Path) -> list[dict]:
    """Parse .ralph/services/metrics.jsonl for service health data.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        List of dicts with keys: service_id, runs, success_count, avg_duration_ms, last_run.
    """
    metrics_path = ralph_dir / "services" / "metrics.jsonl"
    if not metrics_path.exists():
        return []

    # Group by service_id
    services: dict[str, dict] = {}
    try:
        for line in metrics_path.read_text().splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                data = json.loads(line)
                sid = data.get("service_id", "unknown")
                if sid not in services:
                    services[sid] = {
                        "service_id": sid,
                        "runs": 0,
                        "success_count": 0,
                        "total_duration_ms": 0,
                        "last_run": "",
                    }
                services[sid]["runs"] += 1
                if data.get("success", False):
                    services[sid]["success_count"] += 1
                services[sid]["total_duration_ms"] += data.get("duration_ms", 0)
                services[sid]["last_run"] = data.get("timestamp", "")
            except json.JSONDecodeError:
                continue
    except OSError:
        pass

    result = []
    for info in services.values():
        runs = info["runs"]
        result.append({
            "service_id": info["service_id"],
            "runs": runs,
            "success_pct": (info["success_count"] / runs * 100) if runs > 0 else 0.0,
            "avg_duration_ms": info["total_duration_ms"] // max(1, runs),
            "last_run": info["last_run"],
        })
    result.sort(key=lambda x: x["service_id"])
    return result


def fmt_tokens(count: int) -> str:
    if count >= 1_000_000:
        return f"{count / 1_000_000:.1f}M"
    elif count >= 1_000:
        return f"{count / 1_000:.1f}K"
    return str(count)


def fmt_cost(cost: float) -> str:
    return f"${cost:.2f}"


def fmt_duration(ms: int) -> str:
    seconds = ms // 1000
    if seconds >= 3600:
        return f"{seconds // 3600}h {(seconds % 3600) // 60}m"
    elif seconds >= 60:
        return f"{seconds // 60}m {seconds % 60}s"
    return f"{seconds}s"


class MetricsPanel(Widget):
    """Metrics panel showing aggregated statistics from all worker logs."""

    DEFAULT_CSS = """
    MetricsPanel {
        height: 1fr;
        width: 100%;
        layout: vertical;
    }

    MetricsPanel .metrics-top {
        height: auto;
        width: 100%;
    }

    MetricsPanel .metrics-section {
        width: 1fr;
        height: auto;
        padding: 0 1;
        border: solid #45475a;
        background: #181825;
        margin: 0 0 0 0;
    }

    MetricsPanel .metrics-workers-table {
        height: auto;
        max-height: 50%;
        border: solid #45475a;
    }

    MetricsPanel .metrics-services {
        height: auto;
        max-height: 30%;
        border: solid #45475a;
    }
    """

    def __init__(self, ralph_dir: Path) -> None:
        super().__init__()
        self.ralph_dir = ralph_dir
        self.metrics: AggregateMetrics = AggregateMetrics()
        self._last_data_hash: str = ""

    def _compute_data_hash(self, metrics: AggregateMetrics) -> str:
        return str((
            metrics.total_workers, metrics.completed_workers, metrics.failed_workers,
            metrics.merged_workers, metrics.total_cost_usd, metrics.total_turns,
            metrics.input_tokens,
        ))

    def _render_summary(self) -> str:
        """Render summary section text."""
        m = self.metrics
        success_rate = 0.0
        finished = m.completed_workers + m.merged_workers + m.failed_workers
        if finished > 0:
            success_rate = (m.completed_workers + m.merged_workers) / finished * 100
        lines = [
            "[bold #cba6f7]SUMMARY[/]",
            (
                f"[#7f849c]Workers:[/] [#a6e3a1]{m.total_workers}[/] "
                f"([#a6e3a1]{m.running_workers}[/] run / [#89b4fa]{m.completed_workers}[/] done / "
                f"[#f38ba8]{m.failed_workers}[/] fail)"
            ),
            (
                f"[#7f849c]Merged:[/] [#6c7086]{m.merged_workers}[/] │ "
                f"[#7f849c]Success:[/] [#a6e3a1]{success_rate:.0f}%[/]"
            ),
            (
                f"[#7f849c]Cost:[/] [#a6e3a1]{fmt_cost(m.total_cost_usd)}[/] │ "
                f"[#7f849c]Time:[/] [#a6e3a1]{fmt_duration(m.total_duration_ms)}[/]"
            ),
        ]
        return "\n".join(lines)

    def _render_git_state(self) -> str:
        """Render git state section text."""
        lines = ["[bold #cba6f7]GIT STATE[/]"]
        git_states = parse_git_state_summary(self.ralph_dir)
        if git_states:
            parts = [f"[#a6adc8]{state}:[/] [#a6e3a1]{count}[/]" for state, count in sorted(git_states.items())]
            for i in range(0, len(parts), 3):
                lines.append(" │ ".join(parts[i:i+3]))
        else:
            lines.append("[#7f849c]No git state data[/]")
        return "\n".join(lines)

    def _render_tokens(self) -> str:
        """Render tokens section text."""
        m = self.metrics
        total_tokens = m.input_tokens + m.output_tokens + m.cache_creation_tokens + m.cache_read_tokens
        lines = [
            "[bold #cba6f7]TOKENS[/]",
            (
                f"[#7f849c]Input:[/] [#a6e3a1]{fmt_tokens(m.input_tokens)}[/] │ "
                f"[#7f849c]Output:[/] [#a6e3a1]{fmt_tokens(m.output_tokens)}[/]"
            ),
            (
                f"[#7f849c]Cache R:[/] [#a6e3a1]{fmt_tokens(m.cache_read_tokens)}[/] │ "
                f"[#7f849c]Cache W:[/] [#a6e3a1]{fmt_tokens(m.cache_creation_tokens)}[/]"
            ),
            f"[#7f849c]Total:[/] [#a6e3a1]{fmt_tokens(total_tokens)}[/]",
        ]
        return "\n".join(lines)

    def _render_pipeline_steps(self) -> str:
        """Render pipeline steps section text."""
        lines = ["[bold #cba6f7]PIPELINE STEPS (avg)[/]"]
        step_durations = parse_pipeline_step_durations(self.ralph_dir)
        if step_durations:
            parts = [
                f"[#a6adc8]{sid}:[/] [#a6e3a1]{fmt_duration(info['avg_ms'])}[/]"
                for sid, info in sorted(step_durations.items())
            ]
            for i in range(0, len(parts), 3):
                lines.append(" │ ".join(parts[i:i+3]))
        else:
            lines.append("[#7f849c]No pipeline step data[/]")
        return "\n".join(lines)

    def _render_conversation(self) -> str:
        """Render conversation stats section text."""
        m = self.metrics
        total_tokens = m.input_tokens + m.output_tokens + m.cache_creation_tokens + m.cache_read_tokens
        avg_turns = m.total_turns / max(1, m.total_workers)
        avg_cost = m.total_cost_usd / max(1, m.total_workers)
        tokens_per_turn = total_tokens // max(1, m.total_turns) if m.total_turns > 0 else 0
        lines = [
            "[bold #cba6f7]CONVERSATION[/]",
            (
                f"[#7f849c]Turns:[/] [#a6e3a1]{m.total_turns}[/] ({avg_turns:.1f} avg) │ "
                f"[#7f849c]Cost/Worker:[/] [#a6e3a1]{fmt_cost(avg_cost)}[/] │ "
                f"[#7f849c]Tokens/Turn:[/] [#a6e3a1]{fmt_tokens(tokens_per_turn)}[/]"
            ),
        ]
        return "\n".join(lines)

    def _render_api_usage(self) -> str:
        """Render API usage section text."""
        api = read_api_usage(self.ralph_dir)
        if api.cycle_prompts == 0 and api.weekly_prompts == 0:
            return "[bold #cba6f7]API USAGE[/]\n[#7f849c]No API usage data[/]"

        lines = ["[bold #cba6f7]API USAGE[/]"]
        if api.cycle_prompts > 0:
            hours_str = f"{api.cycle_hours:.0f}h" if api.cycle_hours >= 1 else "<1h"
            lines.append(
                f"[#7f849c]{hours_str} Cycle:[/] [#a6e3a1]{api.cycle_prompts}[/] prompts │ "
                f"[#7f849c]In:[/] [#a6e3a1]{fmt_tokens(api.cycle_input_tokens)}[/] │ "
                f"[#7f849c]Out:[/] [#a6e3a1]{fmt_tokens(api.cycle_output_tokens)}[/]"
            )
        if api.weekly_prompts > 0:
            lines.append(
                f"[#7f849c]Weekly:[/] [#a6e3a1]{api.weekly_prompts}[/] prompts │ "
                f"[#7f849c]In:[/] [#a6e3a1]{fmt_tokens(api.weekly_input_tokens)}[/] │ "
                f"[#7f849c]Out:[/] [#a6e3a1]{fmt_tokens(api.weekly_output_tokens)}[/]"
            )
        return "\n".join(lines)

    def _render_memory_section(self) -> str:
        """Render memory stats section text."""
        mem = read_memory_stats(self.ralph_dir)
        if mem.tasks_analyzed == 0:
            return "[bold #cba6f7]MEMORY (historical)[/]\n[#7f849c]No memory data[/]"

        # Format avg duration
        s = int(mem.avg_total_duration_s)
        if s >= 3600:
            dur_str = f"{s // 3600}h {(s % 3600) // 60}m"
        elif s >= 60:
            dur_str = f"{s // 60}m {s % 60}s"
        else:
            dur_str = f"{s}s"

        lines = [
            "[bold #cba6f7]MEMORY (historical)[/]",
            (
                f"[#7f849c]Tasks:[/] [#a6e3a1]{mem.tasks_analyzed}[/] │ "
                f"[#7f849c]Success:[/] [#a6e3a1]{mem.success_rate:.0f}%[/] │ "
                f"[#7f849c]Avg Fix Cycles:[/] [#a6e3a1]{mem.avg_fix_cycles:.1f}[/] │ "
                f"[#7f849c]Avg Duration:[/] [#a6e3a1]{dur_str}[/]"
            ),
        ]
        return "\n".join(lines)

    def compose(self) -> ComposeResult:
        self._load_metrics()

        # Top sections in a 2x2 grid
        with Horizontal(classes="metrics-top"):
            yield Static(self._render_summary(), markup=True, classes="metrics-section", id="metrics-summary")
            yield Static(self._render_git_state(), markup=True, classes="metrics-section", id="metrics-git-state")

        with Horizontal(classes="metrics-top"):
            yield Static(self._render_tokens(), markup=True, classes="metrics-section", id="metrics-tokens")
            yield Static(self._render_pipeline_steps(), markup=True, classes="metrics-section", id="metrics-pipeline")

        with Horizontal(classes="metrics-top"):
            yield Static(self._render_conversation(), markup=True, classes="metrics-section", id="metrics-conversation")
            yield Static(self._render_api_usage(), markup=True, classes="metrics-section", id="metrics-api-usage")

        yield Static(self._render_memory_section(), markup=True, classes="metrics-section", id="metrics-memory")

        # Workers by cost table (always created, populated in on_mount)
        table = DataTable(id="metrics-workers-table", classes="metrics-workers-table")
        table.cursor_type = "row"
        table.zebra_stripes = True
        yield table

        # Service health table (always created, populated in on_mount)
        svc_table = DataTable(id="metrics-services-table", classes="metrics-services")
        svc_table.cursor_type = "row"
        yield svc_table

    def on_mount(self) -> None:
        """Populate data tables after mount."""
        self._populate_workers_table()
        self._populate_services_table()

    def _populate_workers_table(self) -> None:
        """Populate the workers-by-cost table."""
        try:
            table = self.query_one("#metrics-workers-table", DataTable)
        except Exception:
            return

        if not table.columns:
            table.add_columns("Status", "Task ID", "Turns", "Tokens", "Cost", "Duration")
        table.clear()

        for wm in self.metrics.worker_summaries[:20]:
            status_color = {
                "running": "#a6e3a1",
                "completed": "#89b4fa",
                "failed": "#f38ba8",
                "stopped": "#7f849c",
                "merged": "#6c7086",
            }.get(wm.status, "#7f849c")

            total_tokens = wm.input_tokens + wm.output_tokens
            table.add_row(
                f"[{status_color}]{wm.status}[/]",
                wm.task_id[:30],
                str(wm.num_turns),
                fmt_tokens(total_tokens),
                fmt_cost(wm.total_cost_usd),
                fmt_duration(wm.duration_ms),
            )

    def _populate_services_table(self) -> None:
        """Populate the service health table."""
        try:
            table = self.query_one("#metrics-services-table", DataTable)
        except Exception:
            return

        if not table.columns:
            table.add_columns("Service", "Runs", "Success%", "Avg Duration", "Last Run")
        table.clear()

        service_data = parse_service_metrics(self.ralph_dir)
        for svc in service_data:
            table.add_row(
                svc["service_id"],
                str(svc["runs"]),
                f"{svc['success_pct']:.0f}%",
                fmt_duration(svc["avg_duration_ms"]),
                format_relative_time(int(svc["last_run"])) if svc["last_run"] else "-",
            )

    def _load_metrics(self) -> None:
        self.metrics = aggregate_worker_metrics(self.ralph_dir)

    def refresh_data(self) -> None:
        self._load_metrics()
        new_hash = self._compute_data_hash(self.metrics)
        if new_hash == self._last_data_hash:
            return
        self._last_data_hash = new_hash
        # Update Static sections in place
        try:
            self.query_one("#metrics-summary", Static).update(self._render_summary())
        except Exception:
            pass
        try:
            self.query_one("#metrics-git-state", Static).update(self._render_git_state())
        except Exception:
            pass
        try:
            self.query_one("#metrics-tokens", Static).update(self._render_tokens())
        except Exception:
            pass
        try:
            self.query_one("#metrics-pipeline", Static).update(self._render_pipeline_steps())
        except Exception:
            pass
        try:
            self.query_one("#metrics-conversation", Static).update(self._render_conversation())
        except Exception:
            pass
        try:
            self.query_one("#metrics-api-usage", Static).update(self._render_api_usage())
        except Exception:
            pass
        try:
            self.query_one("#metrics-memory", Static).update(self._render_memory_section())
        except Exception:
            pass
        # Re-populate data tables
        self._populate_workers_table()
        self._populate_services_table()
