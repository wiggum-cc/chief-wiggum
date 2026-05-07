"""Main Textual application for Wiggum TUI."""

from pathlib import Path

from textual.app import App, ComposeResult
from textual.binding import Binding
from textual.widgets import Footer, TabbedContent, TabPane, Tree, OptionList

from .themes.htop import HTOP_THEME
from .widgets.header import WiggumHeader
from .widgets.kanban_panel import KanbanPanel
from .widgets.workers_panel import WorkersPanel
from .widgets.logs_panel import LogsPanel
from .widgets.metrics_panel import MetricsPanel
from .widgets.conversation_panel import ConversationPanel
from .widgets.plan_panel import PlanPanel
from .widgets.memory_panel import MemoryPanel
from .data.watcher import RalphWatcher
from .data.worker_status_service import WorkerStatusService
from .data.worker_scanner import get_orchestrator_status, get_worker_counts
from .data.status_reader import read_api_usage, read_memory_stats, aggregate_session_cost
from .messages import NavigateToTask


class WiggumApp(App):
    """Main Wiggum TUI application."""

    TITLE = "Wiggum Monitor"
    CSS = HTOP_THEME

    BINDINGS = [
        Binding("q", "quit", "Quit"),
        Binding("1", "switch_tab('kanban')", "Kanban", show=True),
        Binding("2", "switch_tab('workers')", "Workers", show=True),
        Binding("3", "switch_tab('logs')", "Logs", show=True),
        Binding("4", "switch_tab('conversations')", "Chat", show=True),
        Binding("5", "switch_tab('plans')", "Plans", show=True),
        Binding("6", "switch_tab('metrics')", "Metrics", show=True),
        Binding("7", "switch_tab('memory')", "Memory", show=True),
        Binding("r", "refresh", "Refresh"),
        Binding("?", "help", "Help"),
        # Vim-style tab navigation
        Binding("h", "prev_tab", "Prev Tab", show=False),
        Binding("l", "next_tab", "Next Tab", show=False),
        Binding("H", "first_tab", "First Tab", show=False),
        Binding("L", "last_tab", "Last Tab", show=False),
    ]

    def __init__(self, ralph_dir: Path) -> None:
        super().__init__()
        self.ralph_dir = ralph_dir
        self.watcher = RalphWatcher(ralph_dir)
        self.worker_service = WorkerStatusService(ralph_dir)
        self._active_tab: str = "kanban"
        self._pending_navigation: tuple[str, str] | None = None

    def compose(self) -> ComposeResult:
        yield WiggumHeader(self.ralph_dir)
        with TabbedContent(initial="kanban"):
            with TabPane("Kanban", id="kanban"):
                yield KanbanPanel(self.ralph_dir)
            with TabPane("Workers", id="workers"):
                yield WorkersPanel(self.ralph_dir)
            with TabPane("Logs", id="logs"):
                yield LogsPanel(self.ralph_dir)
            with TabPane("Conversations", id="conversations"):
                yield ConversationPanel(self.ralph_dir)
            with TabPane("Plans", id="plans"):
                yield PlanPanel(self.ralph_dir)
            with TabPane("Metrics", id="metrics"):
                yield MetricsPanel(self.ralph_dir)
            with TabPane("Memory", id="memory"):
                yield MemoryPanel(self.ralph_dir)
        yield Footer()

    async def on_mount(self) -> None:
        """Start file watcher on mount."""
        # Register callbacks for each panel
        self.watcher.on_kanban_change(self._on_kanban_change)
        self.watcher.on_workers_change(self._on_workers_change)
        self.watcher.on_logs_change(self._on_logs_change)
        self.watcher.on_metrics_change(self._on_metrics_change)

        # Start watching
        self.watcher.start()

        # Set up header update timer (fast - 1s)
        self.set_interval(1, self._update_header)

        # Set up header slow update timer (5s for expensive reads)
        self.set_interval(5, self._update_header_slow)

        # Set up 1-second auto-refresh timer for active panel only
        self.set_interval(1, self._refresh_active_panel)

    def on_unmount(self) -> None:
        """Stop file watcher on unmount."""
        self.watcher.stop()

    async def _on_kanban_change(self) -> None:
        """Handle kanban.md changes."""
        try:
            panel = self.query_one(KanbanPanel)
            panel.refresh_data()
        except Exception:
            pass

    async def _on_workers_change(self) -> None:
        """Handle workers directory changes."""
        try:
            panel = self.query_one(WorkersPanel)
            panel.refresh_data()
        except Exception:
            pass

    async def _on_logs_change(self) -> None:
        """Handle log file changes."""
        try:
            panel = self.query_one(LogsPanel)
            panel.refresh_data()
        except Exception:
            pass

    async def _on_metrics_change(self) -> None:
        """Handle metrics.json changes."""
        try:
            panel = self.query_one(MetricsPanel)
            panel.refresh_data()
        except Exception:
            pass

    def _update_header(self) -> None:
        """Update header with fast-changing data (worker counts)."""
        try:
            header = self.query_one(WiggumHeader)
            workers = self.worker_service.get_workers()
            counts = get_worker_counts(workers)
            header.update_stats(
                worker_count=counts.get("total", 0),
                running_count=counts.get("running", 0),
            )
        except Exception:
            pass

    def _update_header_slow(self) -> None:
        """Update header with slow-changing data (orchestrator, API, costs)."""
        try:
            header = self.query_one(WiggumHeader)

            # Orchestrator status
            orch_running, _ = get_orchestrator_status(self.ralph_dir)

            # API usage
            api_usage = read_api_usage(self.ralph_dir)

            # Memory stats for success rate
            mem_stats = read_memory_stats(self.ralph_dir)

            # Aggregated session cost
            total_cost = aggregate_session_cost(self.ralph_dir)

            header.update_slow_stats(
                orchestrator_running=orch_running,
                api_usage=api_usage,
                success_rate=mem_stats.success_rate,
                total_cost=total_cost,
            )
        except Exception:
            pass

    def _refresh_active_panel(self) -> None:
        """Auto-refresh only the currently visible panel every second."""
        try:
            if self._active_tab == "kanban":
                self.query_one(KanbanPanel).refresh_data()
            elif self._active_tab == "workers":
                self.query_one(WorkersPanel).refresh_data()
            elif self._active_tab == "logs":
                self.query_one(LogsPanel).refresh_data()
            elif self._active_tab == "metrics":
                self.query_one(MetricsPanel).refresh_data()
            elif self._active_tab == "conversations":
                self.query_one(ConversationPanel).refresh_data()
            elif self._active_tab == "plans":
                self.query_one(PlanPanel).refresh_data()
            elif self._active_tab == "memory":
                self.query_one(MemoryPanel).refresh_data()
        except Exception:
            pass

    def on_tabbed_content_tab_activated(self, event: TabbedContent.TabActivated) -> None:
        """Handle tab changes - track active tab and refresh newly visible panel."""
        self._active_tab = event.pane.id or "kanban"
        # Refresh the newly active panel immediately
        self._refresh_active_panel()

        # Apply pending navigation after refresh so selection isn't overwritten
        if self._pending_navigation:
            target, task_id = self._pending_navigation
            if event.pane.id == target:
                self._pending_navigation = None
                self._select_in_panel(target, task_id)

    TAB_ORDER = ["kanban", "workers", "logs", "conversations", "plans", "metrics", "memory"]

    def action_switch_tab(self, tab_id: str) -> None:
        """Switch to a specific tab."""
        tabbed = self.query_one(TabbedContent)
        tabbed.active = tab_id

    def action_prev_tab(self) -> None:
        """Switch to previous tab (vim h)."""
        tabbed = self.query_one(TabbedContent)
        current = tabbed.active
        try:
            idx = self.TAB_ORDER.index(current)
            new_idx = (idx - 1) % len(self.TAB_ORDER)
            tabbed.active = self.TAB_ORDER[new_idx]
        except ValueError:
            pass

    def action_next_tab(self) -> None:
        """Switch to next tab (vim l)."""
        tabbed = self.query_one(TabbedContent)
        current = tabbed.active
        try:
            idx = self.TAB_ORDER.index(current)
            new_idx = (idx + 1) % len(self.TAB_ORDER)
            tabbed.active = self.TAB_ORDER[new_idx]
        except ValueError:
            pass

    def action_first_tab(self) -> None:
        """Switch to first tab (vim H)."""
        tabbed = self.query_one(TabbedContent)
        tabbed.active = self.TAB_ORDER[0]

    def action_last_tab(self) -> None:
        """Switch to last tab (vim L)."""
        tabbed = self.query_one(TabbedContent)
        tabbed.active = self.TAB_ORDER[-1]

    def action_refresh(self) -> None:
        """Manually refresh all panels."""
        try:
            self.query_one(KanbanPanel).refresh_data()
        except Exception:
            pass
        try:
            self.query_one(WorkersPanel).refresh_data()
        except Exception:
            pass
        try:
            self.query_one(LogsPanel).refresh_data()
        except Exception:
            pass
        try:
            self.query_one(MetricsPanel).refresh_data()
        except Exception:
            pass
        try:
            self.query_one(ConversationPanel).refresh_data()
        except Exception:
            pass
        try:
            self.query_one(PlanPanel).refresh_data()
        except Exception:
            pass
        try:
            self.query_one(MemoryPanel).refresh_data()
        except Exception:
            pass

    def _select_in_panel(self, target: str, task_id: str) -> None:
        """Select a task in the target panel and focus it.

        Explicitly moving focus to the target panel prevents Textual's focus
        management from switching back to the previous tab (where the modal
        dismiss restored focus to a kanban TaskCard).
        """
        try:
            if target == "plans":
                panel = self.query_one(PlanPanel)
                panel.select_by_task_id(task_id)
                panel.query_one("#plan-option-list", OptionList).focus()
            elif target == "conversations":
                panel = self.query_one(ConversationPanel)
                panel.select_by_task_id(task_id)
                panel.query_one("#conv-tree", Tree).focus()
        except Exception:
            pass

    def on_navigate_to_task(self, message: NavigateToTask) -> None:
        """Handle cross-tab navigation to a specific task."""
        target = message.target_tab
        task_id = message.task_id

        tabbed = self.query_one(TabbedContent)

        if tabbed.active == target:
            # Already on the target tab — select immediately
            self._refresh_active_panel()
            self._select_in_panel(target, task_id)
        else:
            # Store pending navigation — selection will be applied after the tab
            # switch triggers on_tabbed_content_tab_activated and refreshes the
            # panel, so the selection isn't overwritten by the first refresh.
            self._pending_navigation = (target, task_id)
            tabbed.active = target

    def action_help(self) -> None:
        """Show help dialog."""
        self.notify(
            "Keyboard shortcuts:\n"
            "1-7: Switch tabs │ h/l: Prev/Next tab │ H/L: First/Last tab\n"
            "j/k: Down/Up │ g/G: Top/Bottom │ Ctrl+d/u: Half page\n"
            "Workers: s-Stop K-Kill c-Chat L-Logs Enter-Detail\n"
            "Tree: h/l-Collapse/Expand o-Toggle e-ExpandAll C-CollapseAll\n"
            "r: Refresh │ q: Quit",
            title="Help",
            timeout=8,
        )
