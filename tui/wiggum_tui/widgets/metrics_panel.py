"""Metrics panel widget showing dashboard cards."""

from pathlib import Path
from textual.app import ComposeResult
from textual.containers import Horizontal, Vertical, Grid
from textual.widgets import Static
from textual.widget import Widget

from ..data.metrics_reader import (
    read_metrics,
    format_tokens,
    format_cost,
    format_duration,
)
from ..data.models import Metrics


class MetricCard(Static):
    """A single metric card."""

    DEFAULT_CSS = """
    MetricCard {
        background: #1e293b;
        border: solid #334155;
        padding: 1;
        height: auto;
        min-height: 5;
    }

    MetricCard .metric-title {
        color: #64748b;
        text-style: bold;
    }

    MetricCard .metric-value {
        color: #22c55e;
        text-style: bold;
    }

    MetricCard .metric-secondary {
        color: #94a3b8;
    }
    """

    def __init__(self, title: str, value: str, secondary: str = "") -> None:
        super().__init__()
        self.title = title
        self.value = value
        self.secondary = secondary

    def render(self) -> str:
        lines = [
            f"[#64748b]{self.title}[/]",
            f"[bold #22c55e]{self.value}[/]",
        ]
        if self.secondary:
            lines.append(f"[#94a3b8]{self.secondary}[/]")
        return "\n".join(lines)


class MetricsPanel(Widget):
    """Metrics panel showing aggregated statistics."""

    DEFAULT_CSS = """
    MetricsPanel {
        height: 1fr;
        width: 100%;
        padding: 1;
        layout: vertical;
        overflow-y: auto;
    }

    MetricsPanel .metrics-grid {
        grid-size: 4;
        grid-gutter: 1;
        height: auto;
    }

    MetricsPanel .section-title {
        color: #f59e0b;
        text-style: bold;
        padding: 1 0;
    }

    MetricsPanel .empty-message {
        text-align: center;
        color: #64748b;
        padding: 2;
    }

    MetricsPanel .workers-list {
        height: 1fr;
        border: solid #334155;
        background: #0f172a;
        padding: 1;
    }

    MetricsPanel .worker-row {
        height: 1;
    }
    """

    def __init__(self, ralph_dir: Path) -> None:
        super().__init__()
        self.ralph_dir = ralph_dir
        self.metrics_path = ralph_dir / "metrics.json"
        self.metrics: Metrics = Metrics()
        self._last_data_hash: str = ""

    def _compute_data_hash(self, metrics: Metrics) -> str:
        """Compute a hash of metrics data for change detection."""
        data = (
            metrics.total_workers,
            metrics.successful_workers,
            metrics.failed_workers,
            metrics.total_cost,
            metrics.total_time_seconds,
        )
        return str(data)

    def compose(self) -> ComposeResult:
        self._load_metrics()

        if self.metrics.total_workers == 0:
            yield Static(
                "No metrics available. Complete some tasks to see metrics.",
                classes="empty-message",
            )
            return

        yield Static("SUMMARY", classes="section-title")
        with Grid(classes="metrics-grid"):
            yield MetricCard(
                "Workers",
                str(self.metrics.total_workers),
                f"{self.metrics.successful_workers} success / {self.metrics.failed_workers} failed",
            )
            yield MetricCard(
                "Success Rate",
                f"{self.metrics.success_rate:.1f}%",
                "",
            )
            yield MetricCard(
                "Total Time",
                format_duration(self.metrics.total_time_seconds),
                self.metrics.total_time,
            )
            yield MetricCard(
                "Total Cost",
                format_cost(self.metrics.total_cost),
                "",
            )

        yield Static("TOKENS", classes="section-title")
        with Grid(classes="metrics-grid"):
            yield MetricCard(
                "Input",
                format_tokens(self.metrics.tokens.input),
                format_cost(self.metrics.cost_breakdown.input),
            )
            yield MetricCard(
                "Output",
                format_tokens(self.metrics.tokens.output),
                format_cost(self.metrics.cost_breakdown.output),
            )
            yield MetricCard(
                "Cache Creation",
                format_tokens(self.metrics.tokens.cache_creation),
                format_cost(self.metrics.cost_breakdown.cache_creation),
            )
            yield MetricCard(
                "Cache Read",
                format_tokens(self.metrics.tokens.cache_read),
                format_cost(self.metrics.cost_breakdown.cache_read),
            )

        yield Static("RECENT WORKERS", classes="section-title")
        with Vertical(classes="workers-list"):
            # Show last 10 workers
            for worker in self.metrics.workers[:10]:
                status_color = "#22c55e" if worker.status == "success" else "#dc2626"
                yield Static(
                    f"[{status_color}]{worker.status:8}[/] │ "
                    f"[#f59e0b]{worker.worker_id[:30]:30}[/] │ "
                    f"[#64748b]{worker.time_spent}[/] │ "
                    f"[#22c55e]{format_cost(worker.cost)}[/]",
                    classes="worker-row",
                )

    def _load_metrics(self) -> None:
        """Load metrics from metrics.json."""
        self.metrics = read_metrics(self.metrics_path)

    def refresh_data(self) -> None:
        """Refresh metrics data and re-render only if data changed."""
        old_metrics = self.metrics
        self._load_metrics()

        # Check if data actually changed
        new_hash = self._compute_data_hash(self.metrics)
        if new_hash == self._last_data_hash:
            return  # No change, skip refresh
        self._last_data_hash = new_hash

        self.remove_children()
        for widget in self.compose():
            self.mount(widget)
