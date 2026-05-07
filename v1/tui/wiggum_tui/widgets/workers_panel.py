"""Workers panel widget with DataTable."""

import time
from pathlib import Path
from textual.app import ComposeResult
from textual.widgets import DataTable, Static
from textual.widget import Widget
from textual.binding import Binding
from textual.message import Message

from ..data.worker_scanner import scan_workers, get_worker_counts
from ..data.models import Worker, WorkerStatus
from ..data.status_reader import read_worker_cost
from ..actions.worker_control import stop_worker, kill_worker
from .filter_sort_bar import FilterSortBar, SortOption, FilterOption


def format_duration(seconds: int) -> str:
    """Format duration in human-readable format.

    Args:
        seconds: Duration in seconds.

    Returns:
        Formatted string like "2h 15m" or "45m 30s" or "10s".
    """
    if seconds < 0:
        return "-"
    hours, remainder = divmod(seconds, 3600)
    minutes, secs = divmod(remainder, 60)
    if hours > 0:
        return f"{hours}h {minutes}m"
    elif minutes > 0:
        return f"{minutes}m {secs}s"
    else:
        return f"{secs}s"


class WorkersPanel(Widget):
    """Workers panel showing all workers in a table."""

    DEFAULT_CSS = """
    WorkersPanel {
        height: 1fr;
        width: 100%;
        layout: vertical;
    }

    WorkersPanel .workers-header {
        height: 1;
        background: #181825;
        padding: 0 1;
    }

    WorkersPanel DataTable {
        height: 1fr;
    }

    WorkersPanel .empty-message {
        text-align: center;
        color: #7f849c;
        padding: 2;
    }
    """

    BINDINGS = [
        Binding("s", "stop_worker", "Stop"),
        Binding("K", "kill_worker", "Kill"),  # Uppercase to avoid conflict with vim k
        Binding("c", "view_conversation", "View Chat"),
        Binding("L", "view_logs", "View Logs"),  # Uppercase to avoid conflict with vim l
        # Vim-style navigation
        Binding("j", "cursor_down", "Down", show=False),
        Binding("k", "cursor_up", "Up", show=False),
        Binding("g", "goto_top", "Top", show=False),
        Binding("G", "goto_bottom", "Bottom", show=False),
        Binding("ctrl+d", "half_page_down", "Half Page Down", show=False),
        Binding("ctrl+u", "half_page_up", "Half Page Up", show=False),
    ]

    class WorkerSelected(Message):
        """Message sent when a worker is selected."""

        def __init__(self, worker: Worker) -> None:
            super().__init__()
            self.worker = worker

    SORT_OPTIONS = [
        SortOption("Status", "status"),
        SortOption("Task ID", "task_id"),
        SortOption("Duration", "duration"),
        SortOption("Agent", "agent"),
        SortOption("Cost", "cost"),
    ]

    FILTER_OPTIONS = [
        FilterOption("Running", "running", active=True),
        FilterOption("Stopped", "stopped", active=True),
        FilterOption("Completed", "completed", active=True),
        FilterOption("Merged", "merged", active=True),
        FilterOption("Failed", "failed", active=True),
    ]

    def __init__(self, ralph_dir: Path) -> None:
        super().__init__()
        self.ralph_dir = ralph_dir
        self._workers_list: list[Worker] = []
        self._filtered_workers: list[Worker] = []
        self._selected_worker: Worker | None = None
        self._last_data_hash: str = ""

    def _compute_data_hash(self, workers: list[Worker]) -> str:
        """Compute a hash of worker data for change detection."""
        data = [
            (
                w.id, w.task_id, w.status.value, w.pid, w.pr_url,
                (w.pipeline_info.pipeline_name, w.pipeline_info.step_id, w.pipeline_info.agent,
                 w.pipeline_info.step_idx, w.pipeline_info.total_steps)
                if w.pipeline_info else None,
            )
            for w in workers
        ]
        return str(data)

    def compose(self) -> ComposeResult:
        self._load_workers()
        self._filtered_workers = list(self._workers_list)
        counts = get_worker_counts(self._workers_list)

        yield Static(
            self._build_header_text(counts),
            classes="workers-header",
        )

        yield FilterSortBar(
            sort_options=list(self.SORT_OPTIONS),
            filter_options=[FilterOption(f.label, f.key, f.active) for f in self.FILTER_OPTIONS],
            show_search=True,
            id="workers-filter-bar",
        )

        table = DataTable(id="workers-table")
        table.cursor_type = "row"
        table.zebra_stripes = True
        yield table

    def on_mount(self) -> None:
        """Set up the data table."""
        try:
            table = self.query_one("#workers-table", DataTable)
            table.add_columns("Status", "Task", "Progress", "Agent", "Cost", "Duration", "PR URL")
            self._populate_table(table)
        except Exception as e:
            self.log.error(f"Failed to populate workers table: {e}")

    def _load_workers(self) -> None:
        """Load workers from .ralph/workers directory."""
        # Use shared worker service if available, otherwise fall back to direct scan
        try:
            self._workers_list = self.app.worker_service.get_workers()
        except AttributeError:
            self._workers_list = scan_workers(self.ralph_dir)

    def _populate_table(self, table: DataTable, preserve_cursor: bool = False) -> None:
        """Populate the table with worker data."""
        # Save cursor position by worker ID before clearing
        cursor_worker_id = None
        if preserve_cursor and table.cursor_row is not None:
            try:
                row_key = table.get_row_at(table.cursor_row)
                cursor_worker_id = str(row_key) if row_key else None
            except Exception:
                pass

        table.clear()
        now_ts = int(time.time())
        display_list = self._filtered_workers
        for worker in display_list:
            is_merged = worker.status == WorkerStatus.MERGED
            dim_open = "[dim]" if is_merged else ""
            dim_close = "[/]" if is_merged else ""

            status_style = self._get_status_style(worker.status)
            status_text = f"[{status_style}]{worker.status.value.upper()}[/]"

            # Format duration from start timestamp
            try:
                duration_secs = now_ts - worker.timestamp
                duration = format_duration(duration_secs)
            except (ValueError, OSError):
                duration = "-"

            pr_url = worker.pr_url or ""
            if len(pr_url) > 30:
                pr_url = pr_url[:27] + "..."

            # Pipeline info: Progress column as "N/M step_id"
            pi = worker.pipeline_info
            if pi and pi.total_steps > 0:
                progress = f"{pi.step_idx + 1}/{pi.total_steps} {pi.step_id}"
            elif pi and pi.step_id:
                progress = pi.step_id
            else:
                progress = "-"

            agent_short = pi.agent_short if pi else ""

            # Cost from cost-tracker.json
            worker_dir = self.ralph_dir / "workers" / worker.id
            if not worker_dir.is_dir():
                worker_dir = self.ralph_dir / "history" / worker.id
            cost = read_worker_cost(worker_dir)
            cost_str = f"${cost:.2f}" if cost is not None else "-"

            table.add_row(
                status_text,
                f"{dim_open}{worker.task_id}{dim_close}",
                f"{dim_open}{progress}{dim_close}",
                f"{dim_open}{agent_short}{dim_close}",
                f"{dim_open}{cost_str}{dim_close}",
                f"{dim_open}{duration}{dim_close}",
                f"{dim_open}{pr_url}{dim_close}",
                key=worker.id,
            )

        # Restore cursor position by worker ID
        if cursor_worker_id:
            for i, worker in enumerate(display_list):
                if worker.id == cursor_worker_id:
                    table.move_cursor(row=i)
                    break

    def _build_header_text(self, counts: dict[str, int]) -> str:
        """Build header text with worker counts."""
        total = counts.get("total", 0)
        running = counts.get("running", 0)
        completed = counts.get("completed", 0)
        merged = counts.get("merged", 0)
        failed = counts.get("failed", 0)
        filtered_count = len(self._filtered_workers)

        text = (
            f"[bold]Workers[/] │ "
            f"[#a6e3a1]Running: {running}[/] │ "
            f"[#89b4fa]Completed: {completed}[/] │ "
            f"[#6c7086]Merged: {merged}[/] │ "
            f"[#f38ba8]Failed: {failed}[/] │ "
            f"Total: {total}"
        )
        if filtered_count != total:
            text += f" │ [#f9e2af]Showing: {filtered_count}[/]"
        return text

    def _apply_filter_sort(
        self,
        workers: list[Worker],
        search_query: str = "",
        sort_key: str = "",
        sort_ascending: bool = True,
        active_filters: list[str] | None = None,
    ) -> list[Worker]:
        """Apply filter, sort, and search to the workers list.

        Args:
            workers: Full workers list.
            search_query: Text to search in worker ID and task ID.
            sort_key: Sort field key.
            sort_ascending: Sort direction.
            active_filters: List of active status filter keys.

        Returns:
            Filtered and sorted list.
        """
        result = list(workers)

        # Apply status filter
        if active_filters is not None:
            result = [w for w in result if w.status.value in active_filters]

        # Apply search
        if search_query:
            q = search_query.lower()
            result = [
                w for w in result
                if q in w.id.lower() or q in w.task_id.lower()
                or (w.pipeline_info and q in w.pipeline_info.agent_short.lower())
            ]

        # Apply sort
        now_ts = int(time.time())
        if sort_key == "status":
            status_order = {
                WorkerStatus.RUNNING: 0,
                WorkerStatus.STOPPED: 1,
                WorkerStatus.COMPLETED: 2,
                WorkerStatus.MERGED: 3,
                WorkerStatus.FAILED: 4,
            }
            result.sort(key=lambda w: status_order.get(w.status, 9), reverse=not sort_ascending)
        elif sort_key == "task_id":
            result.sort(key=lambda w: w.task_id, reverse=not sort_ascending)
        elif sort_key == "duration":
            result.sort(key=lambda w: now_ts - w.timestamp, reverse=not sort_ascending)
        elif sort_key == "agent":
            result.sort(
                key=lambda w: (w.pipeline_info.agent_short if w.pipeline_info else ""),
                reverse=not sort_ascending,
            )
        elif sort_key == "cost":
            def _get_cost(w: Worker) -> float:
                worker_dir = self.ralph_dir / "workers" / w.id
                if not worker_dir.is_dir():
                    worker_dir = self.ralph_dir / "history" / w.id
                c = read_worker_cost(worker_dir)
                return c if c is not None else 0.0
            result.sort(key=_get_cost, reverse=not sort_ascending)

        return result

    def on_filter_sort_bar_changed(self, event: FilterSortBar.Changed) -> None:
        """Handle filter/sort bar state changes."""
        self._filtered_workers = self._apply_filter_sort(
            self._workers_list,
            search_query=event.search_query,
            sort_key=event.sort_key,
            sort_ascending=event.sort_ascending,
            active_filters=event.active_filters,
        )
        # Update header to show filtered count
        counts = get_worker_counts(self._workers_list)
        try:
            header = self.query_one(".workers-header", Static)
            header.update(self._build_header_text(counts))
        except Exception:
            pass

        # Update table
        try:
            table = self.query_one("#workers-table", DataTable)
            self._populate_table(table, preserve_cursor=True)
        except Exception:
            pass

    def _get_status_style(self, status: WorkerStatus) -> str:
        """Get Rich style for a status."""
        return {
            WorkerStatus.RUNNING: "#a6e3a1",
            WorkerStatus.STOPPED: "#7f849c",
            WorkerStatus.COMPLETED: "#89b4fa",
            WorkerStatus.FAILED: "#f38ba8",
            WorkerStatus.MERGED: "#6c7086",
        }.get(status, "#7f849c")

    def _get_selected_worker(self) -> Worker | None:
        """Get the currently selected worker."""
        try:
            table = self.query_one("#workers-table", DataTable)
            if table.cursor_row is not None and table.cursor_row < len(self._filtered_workers):
                return self._filtered_workers[table.cursor_row]
        except Exception:
            pass
        return None

    def on_data_table_row_selected(self, event: DataTable.RowSelected) -> None:
        """Handle Enter on a table row - open detail modal."""
        self.action_open_detail()

    def action_open_detail(self) -> None:
        """Open detail modal for selected worker."""
        worker = self._get_selected_worker()
        if not worker:
            self.app.notify("No worker selected", severity="warning")
            return

        from .kanban_panel import TaskDetailModal
        from ..data.models import Task, TaskStatus
        from ..messages import NavigateToTask

        # Build a minimal Task from the worker's info
        status_map = {
            WorkerStatus.RUNNING: TaskStatus.IN_PROGRESS,
            WorkerStatus.COMPLETED: TaskStatus.COMPLETE,
            WorkerStatus.FAILED: TaskStatus.FAILED,
            WorkerStatus.MERGED: TaskStatus.COMPLETE,
            WorkerStatus.STOPPED: TaskStatus.IN_PROGRESS,
        }
        task = Task(
            id=worker.task_id,
            title=worker.task_id,
            status=status_map.get(worker.status, TaskStatus.IN_PROGRESS),
        )

        def _handle_result(result: tuple | None) -> None:
            if result is not None:
                task_id, target = result
                self.post_message(NavigateToTask(task_id=task_id, target_tab=target))

        self.app.push_screen(
            TaskDetailModal(task, ralph_dir=self.ralph_dir, worker=worker),
            _handle_result,
        )

    def action_stop_worker(self) -> None:
        """Stop the selected worker."""
        worker = self._get_selected_worker()
        if not worker:
            self.app.notify("No worker selected", severity="warning")
            return

        if worker.status != WorkerStatus.RUNNING:
            self.app.notify("Worker is not running", severity="warning")
            return

        if stop_worker(worker.id):
            self.app.notify(f"Stopping {worker.id}")
            self.refresh_data()
        else:
            self.app.notify(f"Failed to stop {worker.id}", severity="error")

    def action_kill_worker(self) -> None:
        """Kill the selected worker."""
        worker = self._get_selected_worker()
        if not worker:
            self.app.notify("No worker selected", severity="warning")
            return

        if worker.status != WorkerStatus.RUNNING:
            self.app.notify("Worker is not running", severity="warning")
            return

        if kill_worker(worker.id):
            self.app.notify(f"Killed {worker.id}")
            self.refresh_data()
        else:
            self.app.notify(f"Failed to kill {worker.id}", severity="error")

    def action_view_conversation(self) -> None:
        """View conversation for selected worker."""
        worker = self._get_selected_worker()
        if worker:
            # Switch to conversations tab and select this worker
            self.app.action_switch_tab("conversations")
            self.post_message(self.WorkerSelected(worker))

    def action_view_logs(self) -> None:
        """View logs for selected worker."""
        worker = self._get_selected_worker()
        if worker:
            self.app.action_switch_tab("logs")
            # Could emit a message to switch log source

    def action_cursor_down(self) -> None:
        """Move cursor down (vim j)."""
        try:
            table = self.query_one("#workers-table", DataTable)
            table.action_cursor_down()
        except Exception:
            pass

    def action_cursor_up(self) -> None:
        """Move cursor up (vim k)."""
        try:
            table = self.query_one("#workers-table", DataTable)
            table.action_cursor_up()
        except Exception:
            pass

    def action_goto_top(self) -> None:
        """Go to first row (vim gg)."""
        try:
            table = self.query_one("#workers-table", DataTable)
            table.move_cursor(row=0)
        except Exception:
            pass

    def action_goto_bottom(self) -> None:
        """Go to last row (vim G)."""
        try:
            table = self.query_one("#workers-table", DataTable)
            if self._filtered_workers:
                table.move_cursor(row=len(self._filtered_workers) - 1)
        except Exception:
            pass

    def action_half_page_down(self) -> None:
        """Move half page down (vim ctrl+d)."""
        try:
            table = self.query_one("#workers-table", DataTable)
            current = table.cursor_row or 0
            new_row = min(current + 10, max(0, len(self._filtered_workers) - 1))
            table.move_cursor(row=new_row)
        except Exception:
            pass

    def action_half_page_up(self) -> None:
        """Move half page up (vim ctrl+u)."""
        try:
            table = self.query_one("#workers-table", DataTable)
            current = table.cursor_row or 0
            new_row = max(current - 10, 0)
            table.move_cursor(row=new_row)
        except Exception:
            pass

    def refresh_data(self) -> None:
        """Refresh worker data and re-render."""
        self._load_workers()

        # Re-apply current filter/sort settings
        try:
            bar = self.query_one("#workers-filter-bar", FilterSortBar)
            self._filtered_workers = self._apply_filter_sort(
                self._workers_list,
                search_query=bar.search_query,
                sort_key=bar.sort_key,
                sort_ascending=bar.sort_ascending,
                active_filters=bar.active_filters,
            )
        except Exception:
            self._filtered_workers = list(self._workers_list)

        # Check if worker state (not duration) actually changed
        new_hash = self._compute_data_hash(self._workers_list)
        state_changed = new_hash != self._last_data_hash
        if state_changed:
            self._last_data_hash = new_hash

        # Update header only when worker state changes (not duration)
        if state_changed:
            try:
                counts = get_worker_counts(self._workers_list)
                header = self.query_one(".workers-header", Static)
                header.update(self._build_header_text(counts))
            except Exception:
                pass

        # Update table while preserving cursor position
        try:
            table = self.query_one("#workers-table", DataTable)
            self._populate_table(table, preserve_cursor=True)
        except Exception:
            pass
