"""Header widget for Wiggum TUI - 2-line status bar."""

from pathlib import Path
from datetime import datetime
from textual.widgets import Static

from ..data.status_reader import ApiUsage


class WiggumHeader(Static):
    """Custom 2-line header showing project info, orchestrator status, and live stats."""

    DEFAULT_CSS = """
    WiggumHeader {
        background: #181825;
        color: #cdd6f4;
        height: 2;
        dock: top;
        padding: 0 1;
    }
    """

    def __init__(self, ralph_dir: Path) -> None:
        super().__init__("")
        self.ralph_dir = ralph_dir
        self.project_dir = ralph_dir.parent
        # Fast-updating fields (1s timer)
        self.worker_count: int = 0
        self.running_count: int = 0
        # Slow-updating fields (5s timer)
        self.orchestrator_running: bool = False
        self.api_usage: ApiUsage = ApiUsage()
        self.success_rate: float = 0.0
        self.total_cost: float = 0.0

    def render(self) -> str:
        """Render 2-line header content."""
        time_str = datetime.now().strftime("%H:%M:%S")
        project_name = self.project_dir.name

        # Orchestrator indicator
        if self.orchestrator_running:
            orch = "[#a6e3a1]●[/]"
        else:
            orch = "[#f38ba8]○[/]"

        # Line 1: project info + orchestrator + worker counts
        line1 = (
            f" WIGGUM MONITOR │ {project_name} │ {time_str} │ "
            f"Orch: {orch} │ "
            f"Workers: [#a6e3a1]{self.running_count}[/] run / {self.worker_count} total"
        )

        # Line 2: API usage + cost + success rate
        api = self.api_usage
        parts = []
        if api.cycle_prompts > 0:
            hours_str = f"{api.cycle_hours:.0f}h" if api.cycle_hours >= 1 else "<1h"
            parts.append(f"API: {api.cycle_prompts} prompts ({hours_str})")
            parts.append(f"In: {_fmt_tokens(api.cycle_input_tokens)}")
        if self.total_cost > 0:
            parts.append(f"Session Cost: [#a6e3a1]${self.total_cost:.2f}[/]")
        if self.success_rate > 0:
            parts.append(f"Success: [#a6e3a1]{self.success_rate:.0f}%[/]")

        if parts:
            line2 = " " + " │ ".join(parts)
        else:
            line2 = " [#7f849c]Waiting for data...[/]"

        return f"{line1}\n{line2}"

    def update_stats(self, worker_count: int, running_count: int) -> None:
        """Update fast-changing stats (called every 1s).

        Args:
            worker_count: Total number of workers.
            running_count: Number of running workers.
        """
        self.worker_count = worker_count
        self.running_count = running_count
        self.refresh()

    def update_slow_stats(
        self,
        orchestrator_running: bool,
        api_usage: ApiUsage,
        success_rate: float,
        total_cost: float,
    ) -> None:
        """Update slow-changing stats (called every 5s).

        Args:
            orchestrator_running: Whether orchestrator PID is alive.
            api_usage: API usage stats.
            success_rate: Overall success rate percentage.
            total_cost: Aggregated session cost in USD.
        """
        self.orchestrator_running = orchestrator_running
        self.api_usage = api_usage
        self.success_rate = success_rate
        self.total_cost = total_cost
        self.refresh()


def _fmt_tokens(count: int) -> str:
    """Format token count in human-readable form."""
    if count >= 1_000_000_000:
        return f"{count / 1_000_000_000:.1f}B"
    if count >= 1_000_000:
        return f"{count / 1_000_000:.1f}M"
    if count >= 1_000:
        return f"{count / 1_000:.1f}K"
    return str(count)
