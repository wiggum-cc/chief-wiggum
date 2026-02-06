"""Logs panel widget with tree-based source selector and log viewer."""

import re
from pathlib import Path
from textual.app import ComposeResult
from textual.containers import Horizontal
from textual.widgets import Static, RichLog, Input, Tree
from textual.widgets.tree import TreeNode
from textual.widget import Widget
from textual.binding import Binding

from ..data.log_reader import (
    LogTailer,
    filter_by_level,
    read_log,
    parse_activity_log,
)
from ..data.models import LogLevel, LogLine
from ..data.worker_scanner import WORKER_PATTERN


class LogsPanel(Widget):
    """Logs panel with tree-based source selector and log viewer."""

    # --- Tree state preservation helpers (shared pattern with ConversationPanel) ---

    @staticmethod
    def _get_node_key(node: TreeNode) -> str:
        """Generate a stable key for a node based on its label content."""
        label = str(node.label)
        # Remove Rich tags for comparison
        clean_label = re.sub(r'\[/?[^\]]*\]', '', label)
        return clean_label[:100]

    def _get_expanded_keys(self, node: TreeNode, parent_key: str = "") -> set[str]:
        """Get set of keys for all expanded nodes using content-based identification."""
        expanded = set()
        node_key = self._get_node_key(node)
        full_key = f"{parent_key}/{node_key}" if parent_key else node_key

        if node.is_expanded:
            expanded.add(full_key)
        for child in node.children:
            expanded.update(self._get_expanded_keys(child, full_key))
        return expanded

    def _restore_expanded_keys(self, node: TreeNode, expanded_keys: set[str], parent_key: str = "") -> None:
        """Restore expanded state using content-based keys."""
        node_key = self._get_node_key(node)
        full_key = f"{parent_key}/{node_key}" if parent_key else node_key

        if full_key in expanded_keys:
            node.expand()
        else:
            node.collapse()
        for child in node.children:
            self._restore_expanded_keys(child, expanded_keys, full_key)

    def _get_cursor_key(self, tree: Tree) -> str | None:
        """Get the key for the currently selected node."""
        if not tree.cursor_node:
            return None
        keys = []
        node = tree.cursor_node
        while node:
            keys.append(self._get_node_key(node))
            node = node.parent
        keys.reverse()
        return "/".join(keys)

    def _restore_cursor_by_key(self, tree: Tree, cursor_key: str | None) -> None:
        """Try to restore cursor position using content-based key."""
        if not cursor_key:
            return
        key_parts = cursor_key.split("/")
        node = tree.root
        for key_part in key_parts[1:]:
            found = False
            for child in node.children:
                if self._get_node_key(child) == key_part:
                    node = child
                    found = True
                    break
            if not found:
                break
        if node != tree.root:
            tree.select_node(node)

    DEFAULT_CSS = """
    LogsPanel {
        height: 1fr;
        width: 100%;
        layout: vertical;
    }

    LogsPanel .logs-header {
        height: 1;
        background: #181825;
        padding: 0 1;
    }

    LogsPanel .logs-body {
        height: 1fr;
        width: 100%;
    }

    LogsPanel .logs-tree {
        width: 35;
        height: 1fr;
        border: solid #45475a;
        background: #181825;
    }

    LogsPanel .logs-viewer-pane {
        width: 1fr;
        height: 1fr;
        layout: vertical;
    }

    LogsPanel .logs-toolbar {
        height: 1;
        background: #181825;
        padding: 0 1;
    }

    LogsPanel RichLog {
        height: 1fr;
        background: #1e1e2e;
        border: solid #45475a;
    }

    LogsPanel Input {
        width: 1fr;
        height: 1;
        border: none !important;
        background: #313244;
        padding: 0 1;
        display: none;
    }

    LogsPanel Input.visible {
        display: block;
        background: #313244;
    }
    """

    BINDINGS = [
        Binding("f", "cycle_filter", "Filter"),
        Binding("slash", "toggle_search", "Search /", priority=True),
        Binding("g", "goto_top", "Top"),
        Binding("G", "goto_bottom", "Bottom"),
        # Vim-style scrolling
        Binding("j", "scroll_down", "Scroll Down", show=False),
        Binding("k", "scroll_up", "Scroll Up", show=False),
        Binding("ctrl+d", "half_page_down", "Half Page Down", show=False),
        Binding("ctrl+u", "half_page_up", "Half Page Up", show=False),
        Binding("ctrl+f", "page_down", "Page Down", show=False),
        Binding("ctrl+b", "page_up", "Page Up", show=False),
    ]

    FILTER_LEVELS = [
        (None, "All Levels"),
        (LogLevel.INFO, "INFO+"),
        (LogLevel.WARN, "WARN+"),
        (LogLevel.ERROR, "ERROR only"),
    ]

    def __init__(self, ralph_dir: Path) -> None:
        super().__init__()
        self.ralph_dir = ralph_dir
        self.current_filter_idx = 0
        self.tailer: LogTailer | None = None
        self._current_log_path: Path | None = None
        self._current_is_activity: bool = False
        self._search_visible: bool = False
        self._search_query: str = ""
        self._tree_sources: dict[str, Path] = {}  # node data key -> Path
        self._last_sources_hash: str = ""

    def compose(self) -> ComposeResult:
        filter_name = self.FILTER_LEVELS[self.current_filter_idx][1]
        yield Static(
            f"[bold]Logs[/] │ Filter: {filter_name} │ [#585b70]/ search  f filter[/]",
            classes="logs-header",
            id="logs-header",
        )

        with Horizontal(classes="logs-body"):
            yield Tree("Sources", id="logs-source-tree", classes="logs-tree")
            with Widget(classes="logs-viewer-pane"):
                yield Input(
                    placeholder="Press / to search logs...",
                    id="logs-search-input",
                )
                yield RichLog(id="log-viewer", highlight=True, markup=True)

    def on_mount(self) -> None:
        """Initialize log viewer and populate source tree."""
        self._populate_source_tree()
        # Select first global log by default
        self._select_log_source(self.ralph_dir / "logs" / "workers.log")
        self.set_interval(2, self._check_new_logs)

    def _populate_source_tree(self) -> None:
        """Populate the source tree with global logs and worker logs."""
        try:
            tree = self.query_one("#logs-source-tree", Tree)

            # Save expanded state and cursor position before clearing
            expanded_keys = self._get_expanded_keys(tree.root)
            cursor_key = self._get_cursor_key(tree)
            had_content = bool(tree.root.children)

            tree.clear()
            self._tree_sources.clear()

            # Global Logs
            global_node = tree.root.add("[#89b4fa]Global Logs[/]", expand=True)

            workers_log = self.ralph_dir / "logs" / "workers.log"
            if workers_log.exists():
                key = "global:workers.log"
                self._tree_sources[key] = workers_log
                global_node.add_leaf("[#cdd6f4]workers.log[/]", data=key)

            audit_log = self.ralph_dir / "logs" / "audit.log"
            if audit_log.exists():
                key = "global:audit.log"
                self._tree_sources[key] = audit_log
                global_node.add_leaf("[#cdd6f4]audit.log[/]", data=key)

            activity_log = self.ralph_dir / "activity.jsonl"
            if activity_log.exists():
                key = "global:activity.jsonl"
                self._tree_sources[key] = activity_log
                global_node.add_leaf("[#cdd6f4]activity.jsonl[/]", data=key)

            # Workers
            workers_dir = self.ralph_dir / "workers"
            if workers_dir.is_dir():
                workers_node = tree.root.add("[#89b4fa]Workers[/]", expand=True)

                worker_dirs = []
                for entry in workers_dir.iterdir():
                    if not entry.name.startswith("worker-") or not entry.is_dir():
                        continue
                    match = WORKER_PATTERN.match(entry.name)
                    if not match:
                        continue
                    task_id, ts_str = match.groups()
                    try:
                        timestamp = int(ts_str)
                    except ValueError:
                        timestamp = 0

                    # Determine status
                    has_pid = (entry / "agent.pid").exists()
                    status = "running" if has_pid else "stopped"
                    if not has_pid:
                        prd_path = entry / "prd.md"
                        if prd_path.exists():
                            try:
                                content = prd_path.read_text()
                                if "- [*]" in content:
                                    status = "failed"
                                elif "- [ ]" not in content:
                                    status = "completed"
                            except OSError:
                                pass

                    worker_dirs.append((entry, task_id, timestamp, status))

                # Sort by timestamp descending (newest first)
                worker_dirs.sort(key=lambda x: x[2], reverse=True)

                for entry, task_id, timestamp, status in worker_dirs:
                    status_color = {
                        "running": "#a6e3a1",
                        "stopped": "#7f849c",
                        "completed": "#89b4fa",
                        "failed": "#f38ba8",
                    }.get(status, "#7f849c")

                    worker_node = workers_node.add(
                        f"[{status_color}]{task_id} ({status})[/]",
                        expand=False,
                    )

                    # worker.log
                    worker_log = entry / "worker.log"
                    if worker_log.exists():
                        key = f"worker:{entry.name}:worker.log"
                        self._tree_sources[key] = worker_log
                        worker_node.add_leaf("[#cdd6f4]worker.log[/]", data=key)

                    # Nested log directories
                    logs_dir = entry / "logs"
                    if logs_dir.is_dir():
                        for log_subdir in sorted(logs_dir.iterdir()):
                            if log_subdir.is_dir():
                                subdir_node = worker_node.add(
                                    f"[#a6adc8]{log_subdir.name}/[/]",
                                    expand=False,
                                )
                                for log_file in sorted(log_subdir.glob("*.log")):
                                    key = f"worker:{entry.name}:{log_subdir.name}/{log_file.name}"
                                    self._tree_sources[key] = log_file
                                    subdir_node.add_leaf(
                                        f"[#cdd6f4]{log_file.name}[/]",
                                        data=key,
                                    )

            # Restore expanded state if we had content before, otherwise use defaults
            if had_content and expanded_keys:
                self._restore_expanded_keys(tree.root, expanded_keys)
                self._restore_cursor_by_key(tree, cursor_key)
            else:
                tree.root.expand()

        except Exception:
            pass

    def _select_log_source(self, path: Path) -> None:
        """Select a log source and display its content.

        Args:
            path: Path to the log file.
        """
        self._current_log_path = path
        self._current_is_activity = path.name.endswith(".jsonl")

        if self._current_is_activity:
            self.tailer = None
            self._load_activity_log()
        else:
            self.tailer = LogTailer(path, max_buffer=1000)
            self._load_logs()

        self._update_header()

    def _load_activity_log(self) -> None:
        """Load and display an activity JSONL log."""
        if not self._current_log_path:
            return
        try:
            log_viewer = self.query_one("#log-viewer", RichLog)
            log_viewer.clear()

            logs = parse_activity_log(self._current_log_path)

            # Apply filter
            min_level = self.FILTER_LEVELS[self.current_filter_idx][0]
            if min_level:
                logs = filter_by_level(logs, min_level)

            # Apply search
            if self._search_query:
                logs = self._search_filter(logs)

            for log in logs:
                self._write_log_line(log_viewer, log)
        except Exception:
            pass

    def _load_logs(self) -> None:
        """Load and display logs from the current tailer."""
        if not self.tailer:
            return

        try:
            log_viewer = self.query_one("#log-viewer", RichLog)
            log_viewer.clear()

            logs = self.tailer.get_new_lines()

            # Apply filter
            min_level = self.FILTER_LEVELS[self.current_filter_idx][0]
            if min_level:
                logs = filter_by_level(logs, min_level)

            # Apply search
            if self._search_query:
                logs = self._search_filter(logs)

            for log in logs:
                self._write_log_line(log_viewer, log)

        except Exception:
            pass

    def _search_filter(self, logs: list[LogLine]) -> list[LogLine]:
        """Filter logs by search query."""
        q = self._search_query.lower()
        return [log for log in logs if q in log.raw.lower()]

    def _write_log_line(self, viewer: RichLog, log: LogLine) -> None:
        """Write a single log line with coloring."""
        if log.level:
            level_colors = {
                LogLevel.DEBUG: "#7f849c",
                LogLevel.INFO: "#89b4fa",
                LogLevel.WARN: "#f9e2af",
                LogLevel.ERROR: "#f38ba8",
            }
            color = level_colors.get(log.level, "#cdd6f4")

            timestamp = f"[#7f849c]{log.timestamp}[/]" if log.timestamp else ""
            level = f"[{color}]{log.level.value}[/]"
            message = f"[#cdd6f4]{log.message}[/]"

            viewer.write(f"{timestamp} {level}: {message}")
        else:
            viewer.write(f"[#7f849c]{log.raw}[/]")

    def _check_new_logs(self) -> None:
        """Check for and display new log lines."""
        if self._current_is_activity:
            return  # Activity logs don't tail

        if not self.tailer:
            return

        try:
            new_logs = self.tailer.get_new_lines()
            if not new_logs:
                return

            log_viewer = self.query_one("#log-viewer", RichLog)

            # Apply filter
            min_level = self.FILTER_LEVELS[self.current_filter_idx][0]
            if min_level:
                new_logs = filter_by_level(new_logs, min_level)

            # Apply search
            if self._search_query:
                new_logs = self._search_filter(new_logs)

            for log in new_logs:
                self._write_log_line(log_viewer, log)

        except Exception:
            pass

    def _update_header(self) -> None:
        """Update header with current settings."""
        try:
            filter_name = self.FILTER_LEVELS[self.current_filter_idx][1]
            source_name = ""
            if self._current_log_path:
                source_name = self._current_log_path.name

            header = self.query_one("#logs-header", Static)
            header.update(
                f"[bold]Logs[/] │ Source: {source_name} │ Filter: {filter_name} │ "
                f"[#585b70]/search  f-filter[/]"
            )
        except Exception:
            pass

    def on_tree_node_selected(self, event: Tree.NodeSelected) -> None:
        """Handle tree node selection to switch log source."""
        node = event.node
        if node.data and isinstance(node.data, str) and node.data in self._tree_sources:
            path = self._tree_sources[node.data]
            self._select_log_source(path)

    def on_input_changed(self, event: Input.Changed) -> None:
        """Handle search input changes."""
        if event.input.id == "logs-search-input":
            self._search_query = event.value
            # Reload logs with search filter
            if self._current_is_activity:
                self._load_activity_log()
            else:
                self._reload_with_filter()

    def _reload_with_filter(self) -> None:
        """Reload all buffered logs with current filter/search applied."""
        if not self.tailer:
            return
        try:
            log_viewer = self.query_one("#log-viewer", RichLog)
            log_viewer.clear()

            logs = self.tailer.get_all_lines()

            min_level = self.FILTER_LEVELS[self.current_filter_idx][0]
            if min_level:
                logs = filter_by_level(logs, min_level)

            if self._search_query:
                logs = self._search_filter(logs)

            for log in logs:
                self._write_log_line(log_viewer, log)
        except Exception:
            pass

    def action_toggle_search(self) -> None:
        """Toggle search input visibility."""
        try:
            search_input = self.query_one("#logs-search-input", Input)
            if self._search_visible:
                self._search_visible = False
                search_input.remove_class("visible")
                search_input.value = ""
                self._search_query = ""
                # Reload without search
                if self._current_is_activity:
                    self._load_activity_log()
                else:
                    self._reload_with_filter()
            else:
                self._search_visible = True
                search_input.add_class("visible")
                search_input.focus()
        except Exception:
            pass

    def action_cycle_filter(self) -> None:
        """Cycle through filter levels."""
        self.current_filter_idx = (self.current_filter_idx + 1) % len(self.FILTER_LEVELS)
        self._update_header()
        if self._current_is_activity:
            self._load_activity_log()
        else:
            self._reload_with_filter()

    def action_goto_top(self) -> None:
        """Scroll to top of logs."""
        try:
            log_viewer = self.query_one("#log-viewer", RichLog)
            log_viewer.scroll_home()
        except Exception:
            pass

    def action_goto_bottom(self) -> None:
        """Scroll to bottom of logs."""
        try:
            log_viewer = self.query_one("#log-viewer", RichLog)
            log_viewer.scroll_end()
        except Exception:
            pass

    def action_scroll_down(self) -> None:
        """Scroll down one line (vim j)."""
        try:
            log_viewer = self.query_one("#log-viewer", RichLog)
            log_viewer.scroll_relative(y=1)
        except Exception:
            pass

    def action_scroll_up(self) -> None:
        """Scroll up one line (vim k)."""
        try:
            log_viewer = self.query_one("#log-viewer", RichLog)
            log_viewer.scroll_relative(y=-1)
        except Exception:
            pass

    def action_half_page_down(self) -> None:
        """Scroll half page down (vim ctrl+d)."""
        try:
            log_viewer = self.query_one("#log-viewer", RichLog)
            log_viewer.scroll_relative(y=log_viewer.size.height // 2)
        except Exception:
            pass

    def action_half_page_up(self) -> None:
        """Scroll half page up (vim ctrl+u)."""
        try:
            log_viewer = self.query_one("#log-viewer", RichLog)
            log_viewer.scroll_relative(y=-(log_viewer.size.height // 2))
        except Exception:
            pass

    def action_page_down(self) -> None:
        """Scroll full page down (vim ctrl+f)."""
        try:
            log_viewer = self.query_one("#log-viewer", RichLog)
            log_viewer.scroll_relative(y=log_viewer.size.height)
        except Exception:
            pass

    def action_page_up(self) -> None:
        """Scroll full page up (vim ctrl+b)."""
        try:
            log_viewer = self.query_one("#log-viewer", RichLog)
            log_viewer.scroll_relative(y=-log_viewer.size.height)
        except Exception:
            pass

    def _compute_sources_hash(self) -> str:
        """Compute a hash of available log sources for change detection."""
        sources = []
        logs_dir = self.ralph_dir / "logs"
        if logs_dir.is_dir():
            sources.extend(sorted(f.name for f in logs_dir.iterdir() if f.is_file()))
        activity = self.ralph_dir / "activity.jsonl"
        if activity.exists():
            sources.append("activity.jsonl")
        workers_dir = self.ralph_dir / "workers"
        if workers_dir.is_dir():
            for entry in sorted(workers_dir.iterdir()):
                if entry.name.startswith("worker-") and entry.is_dir():
                    sources.append(entry.name)
        return str(sources)

    def refresh_data(self) -> None:
        """Refresh log display."""
        self._check_new_logs()
        # Only rebuild tree when sources change (new workers, new log files)
        new_hash = self._compute_sources_hash()
        if new_hash != self._last_sources_hash:
            self._last_sources_hash = new_hash
            self._populate_source_tree()
