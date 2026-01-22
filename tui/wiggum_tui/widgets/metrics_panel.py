"""Metrics panel widget showing aggregate dashboard from worker logs."""

import json
from pathlib import Path
from dataclasses import dataclass, field
from textual.app import ComposeResult
from textual.widgets import Static
from textual.widget import Widget

from ..data.worker_scanner import scan_workers
from ..data.models import WorkerStatus


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
    total_turns: int = 0
    total_cost_usd: float = 0.0
    total_duration_ms: int = 0
    input_tokens: int = 0
    output_tokens: int = 0
    cache_creation_tokens: int = 0
    cache_read_tokens: int = 0
    worker_summaries: list[WorkerLogMetrics] = field(default_factory=list)


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


def aggregate_worker_metrics(ralph_dir: Path) -> AggregateMetrics:
    """Aggregate metrics from all worker logs."""
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

        worker_dir = ralph_dir / "workers" / worker.id
        logs_dir = worker_dir / "logs"

        worker_metrics = WorkerLogMetrics(
            worker_id=worker.id,
            task_id=worker.task_id,
            status=worker.status.value,
        )

        if logs_dir.is_dir():
            for log_file in logs_dir.glob("*.log"):
                for result in parse_log_metrics(log_file):
                    worker_metrics.num_turns += result.get("num_turns", 0)
                    worker_metrics.total_cost_usd += result.get("total_cost_usd", 0.0)
                    worker_metrics.duration_ms += result.get("duration_ms", 0)
                    usage = result.get("usage", {})
                    worker_metrics.input_tokens += usage.get("input_tokens", 0)
                    worker_metrics.output_tokens += usage.get("output_tokens", 0)
                    worker_metrics.cache_creation_tokens += usage.get("cache_creation_input_tokens", 0)
                    worker_metrics.cache_read_tokens += usage.get("cache_read_input_tokens", 0)

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
    return metrics


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
        padding: 1;
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
            metrics.total_cost_usd, metrics.total_turns, metrics.input_tokens,
        ))

    def compose(self) -> ComposeResult:
        self._load_metrics()
        m = self.metrics

        total_tokens = m.input_tokens + m.output_tokens + m.cache_creation_tokens + m.cache_read_tokens

        success_rate = 0.0
        if m.completed_workers + m.failed_workers > 0:
            success_rate = m.completed_workers / (m.completed_workers + m.failed_workers) * 100

        # Build dashboard as rich text
        lines = []
        lines.append("[bold #cba6f7]═══ SUMMARY ═══[/]")
        lines.append(
            f"[#7f849c]Workers:[/] [#a6e3a1]{m.total_workers}[/] "
            f"([#a6e3a1]{m.running_workers}[/] run / [#89b4fa]{m.completed_workers}[/] done / [#f38ba8]{m.failed_workers}[/] fail) │ "
            f"[#7f849c]Success:[/] [#a6e3a1]{success_rate:.0f}%[/] │ "
            f"[#7f849c]Time:[/] [#a6e3a1]{fmt_duration(m.total_duration_ms)}[/] │ "
            f"[#7f849c]Cost:[/] [#a6e3a1]{fmt_cost(m.total_cost_usd)}[/]"
        )
        lines.append("")
        lines.append("[bold #cba6f7]═══ TOKENS ═══[/]")
        lines.append(
            f"[#7f849c]Input:[/] [#a6e3a1]{fmt_tokens(m.input_tokens)}[/] │ "
            f"[#7f849c]Output:[/] [#a6e3a1]{fmt_tokens(m.output_tokens)}[/] │ "
            f"[#7f849c]Cache Create:[/] [#a6e3a1]{fmt_tokens(m.cache_creation_tokens)}[/] │ "
            f"[#7f849c]Cache Read:[/] [#a6e3a1]{fmt_tokens(m.cache_read_tokens)}[/] │ "
            f"[#7f849c]Total:[/] [#a6e3a1]{fmt_tokens(total_tokens)}[/]"
        )
        lines.append("")
        lines.append("[bold #cba6f7]═══ CONVERSATION ═══[/]")
        avg_turns = m.total_turns / max(1, m.total_workers)
        avg_cost = m.total_cost_usd / max(1, m.total_workers)
        tokens_per_turn = total_tokens // max(1, m.total_turns) if m.total_turns > 0 else 0
        lines.append(
            f"[#7f849c]Turns:[/] [#a6e3a1]{m.total_turns}[/] ({avg_turns:.1f} avg) │ "
            f"[#7f849c]Cost/Worker:[/] [#a6e3a1]{fmt_cost(avg_cost)}[/] │ "
            f"[#7f849c]Tokens/Turn:[/] [#a6e3a1]{fmt_tokens(tokens_per_turn)}[/]"
        )

        if m.worker_summaries:
            lines.append("")
            lines.append("[bold #cba6f7]═══ WORKERS BY COST ═══[/]")
            for wm in m.worker_summaries[:15]:
                status_color = {
                    "running": "#a6e3a1",
                    "completed": "#89b4fa",
                    "failed": "#f38ba8",
                    "stopped": "#7f849c",
                }.get(wm.status, "#7f849c")
                lines.append(
                    f"[{status_color}]{wm.status:10}[/] │ "
                    f"[#cba6f7]{wm.task_id[:30]:30}[/] │ "
                    f"[#7f849c]{wm.num_turns:3} turns[/] │ "
                    f"[#7f849c]{fmt_tokens(wm.input_tokens + wm.output_tokens):>8}[/] │ "
                    f"[#a6e3a1]{fmt_cost(wm.total_cost_usd)}[/]"
                )

        yield Static("\n".join(lines), markup=True)

    def _load_metrics(self) -> None:
        self.metrics = aggregate_worker_metrics(self.ralph_dir)

    def refresh_data(self) -> None:
        self._load_metrics()
        new_hash = self._compute_data_hash(self.metrics)
        if new_hash == self._last_data_hash:
            return
        self._last_data_hash = new_hash
        self.remove_children()
        for widget in self.compose():
            self.mount(widget)
