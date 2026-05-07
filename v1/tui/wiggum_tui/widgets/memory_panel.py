"""Memory panel widget showing the project's learning system."""

from pathlib import Path
from textual.app import ComposeResult
from textual.containers import Horizontal
from textual.widgets import Static, DataTable, Tree
from textual.widget import Widget
from textual.binding import Binding

from ..data.memory_reader import (
    read_all_agent_stats,
    read_agent_observations,
    read_all_task_memories,
    read_task_analysis,
    read_pattern_tree,
    read_pattern_content,
    read_escalated,
    AgentStats,
    TaskMemory,
)
from ..data.status_reader import read_memory_stats


def _fmt_duration(seconds: float) -> str:
    """Format duration in human-readable form."""
    s = int(seconds)
    if s >= 3600:
        return f"{s // 3600}h {(s % 3600) // 60}m"
    if s >= 60:
        return f"{s // 60}m {s % 60}s"
    return f"{s}s"


class MemoryPanel(Widget):
    """Memory panel showing agent stats, task history, patterns, and escalated issues."""

    DEFAULT_CSS = """
    MemoryPanel {
        height: 1fr;
        width: 100%;
        layout: vertical;
    }

    MemoryPanel .memory-header {
        height: 1;
        background: #181825;
        padding: 0 1;
    }

    MemoryPanel .memory-body {
        height: 1fr;
        width: 100%;
    }

    MemoryPanel #memory-tree {
        width: 25;
        min-width: 20;
        max-width: 35;
        height: 1fr;
        border-right: solid #45475a;
        background: #1e1e2e;
    }

    MemoryPanel #memory-content {
        width: 1fr;
        height: 1fr;
        padding: 0 1;
        overflow-y: auto;
    }

    MemoryPanel #memory-agent-table {
        height: 1fr;
    }

    MemoryPanel #memory-detail {
        height: 1fr;
    }
    """

    BINDINGS = [
        Binding("j", "cursor_down", "Down", show=False),
        Binding("k", "cursor_up", "Up", show=False),
        Binding("g", "goto_top", "Top", show=False),
        Binding("G", "goto_bottom", "Bottom", show=False),
    ]

    def __init__(self, ralph_dir: Path) -> None:
        super().__init__()
        self.ralph_dir = ralph_dir
        self._agent_stats: list[AgentStats] = []
        self._task_memories: list[TaskMemory] = []

    def compose(self) -> ComposeResult:
        # Header bar with global stats
        stats = read_memory_stats(self.ralph_dir)
        duration_str = _fmt_duration(stats.avg_total_duration_s) if stats.avg_total_duration_s > 0 else "-"
        header_text = (
            f"[bold]Memory[/] │ "
            f"Tasks: [#a6e3a1]{stats.tasks_analyzed}[/] │ "
            f"Success: [#a6e3a1]{stats.success_rate:.0f}%[/] │ "
            f"Avg Duration: [#a6e3a1]{duration_str}[/]"
        )
        yield Static(header_text, markup=True, classes="memory-header", id="memory-stats-header")

        with Horizontal(classes="memory-body"):
            # Left sidebar tree
            tree: Tree[str] = Tree("Memory", id="memory-tree")
            tree.root.expand()
            self._build_tree(tree)
            yield tree

            # Right content area - starts with agent table
            table = DataTable(id="memory-agent-table")
            table.cursor_type = "row"
            table.zebra_stripes = True
            yield table

            # Detail view (hidden initially)
            yield Static("", markup=True, id="memory-detail")

    def on_mount(self) -> None:
        """Populate agent table on mount."""
        self._populate_agent_table()
        # Hide detail view initially
        try:
            detail = self.query_one("#memory-detail", Static)
            detail.display = False
        except Exception:
            pass

    def _build_tree(self, tree: Tree[str]) -> None:
        """Build the sidebar tree with categories."""
        root = tree.root

        # Overview section
        overview = root.add("Overview", data="overview")
        overview.add_leaf("Global Stats", data="overview:stats")
        escalated = read_escalated(self.ralph_dir)
        overview.add_leaf(f"Escalated ({escalated.open_count})", data="overview:escalated")
        overview.expand()

        # Agents section
        self._agent_stats = read_all_agent_stats(self.ralph_dir)
        agents_node = root.add(f"Agents ({len(self._agent_stats)})", data="agents")
        for agent in self._agent_stats:
            agents_node.add_leaf(
                f"{agent.agent_type} ({agent.pass_rate:.0f}%)",
                data=f"agent:{agent.agent_type}",
            )
        agents_node.expand()

        # Tasks section
        self._task_memories = read_all_task_memories(self.ralph_dir)
        tasks_node = root.add(f"Tasks ({len(self._task_memories)})", data="tasks")
        for task in self._task_memories:
            indicator = "[#a6e3a1]✓[/]" if task.outcome == "success" else "[#f38ba8]✗[/]"
            tasks_node.add_leaf(f"{task.task_id} {indicator}", data=f"task:{task.task_id}")
        tasks_node.expand()

        # Patterns section
        pattern_tree = read_pattern_tree(self.ralph_dir)
        if pattern_tree:
            patterns_node = root.add("Patterns", data="patterns")
            for category, entries in pattern_tree.items():
                cat_node = patterns_node.add(f"{category.title()} ({len(entries)})", data=f"pattern_cat:{category}")
                for entry in entries:
                    cat_node.add_leaf(entry.name, data=f"pattern:{entry.file_path}")
            patterns_node.expand()

    def _populate_agent_table(self) -> None:
        """Populate the agent performance table."""
        try:
            table = self.query_one("#memory-agent-table", DataTable)
        except Exception:
            return

        if not table.columns:
            table.add_columns("Agent", "Runs", "Pass%", "Fix%", "Fail%", "Avg Iter", "Avg Dur")
        table.clear()

        stats = self._agent_stats or read_all_agent_stats(self.ralph_dir)
        for agent in stats:
            table.add_row(
                agent.agent_type,
                str(agent.runs),
                f"{agent.pass_rate:.0f}",
                f"{agent.fix_rate:.0f}",
                f"{agent.fail_rate:.0f}",
                f"{agent.avg_iterations:.1f}",
                _fmt_duration(agent.avg_duration_s),
            )

    def _show_table(self) -> None:
        """Show agent table, hide detail."""
        try:
            self.query_one("#memory-agent-table", DataTable).display = True
            self.query_one("#memory-detail", Static).display = False
        except Exception:
            pass

    def _show_detail(self, content: str) -> None:
        """Show detail content, hide table."""
        try:
            self.query_one("#memory-agent-table", DataTable).display = False
            detail = self.query_one("#memory-detail", Static)
            detail.update(content)
            detail.display = True
        except Exception:
            pass

    def on_tree_node_selected(self, event: Tree.NodeSelected) -> None:
        """Handle tree node selection."""
        data = event.node.data
        if not data or not isinstance(data, str):
            return

        if data in ("overview", "overview:stats", "agents"):
            self._show_table()
        elif data == "overview:escalated":
            escalated = read_escalated(self.ralph_dir)
            if escalated.content:
                self._show_detail(f"[bold #cba6f7]ESCALATED ISSUES[/]\n\n{_escape_markup(escalated.content)}")
            else:
                self._show_detail("[#7f849c]No escalated issues[/]")
        elif data.startswith("agent:"):
            agent_name = data[6:]
            self._show_agent_detail(agent_name)
        elif data.startswith("task:"):
            task_id = data[5:]
            self._show_task_detail(task_id)
        elif data.startswith("pattern:"):
            file_path = data[8:]
            content = read_pattern_content(file_path)
            if content:
                self._show_detail(f"[bold #cba6f7]PATTERN[/]\n\n{_escape_markup(content)}")
            else:
                self._show_detail("[#7f849c]Pattern file not found[/]")
        elif data.startswith("pattern_cat:"):
            # Show category overview
            self._show_table()

    def _show_agent_detail(self, agent_name: str) -> None:
        """Show detail for a specific agent."""
        # Find stats
        stats = None
        for a in self._agent_stats:
            if a.agent_type == agent_name:
                stats = a
                break

        lines = [f"[bold #cba6f7]{agent_name}[/]"]
        if stats:
            lines.append(
                f"Runs: [#a6e3a1]{stats.runs}[/] │ "
                f"Pass: [#a6e3a1]{stats.pass_rate:.0f}%[/] │ "
                f"Fix: [#f9e2af]{stats.fix_rate:.0f}%[/] │ "
                f"Fail: [#f38ba8]{stats.fail_rate:.0f}%[/]"
            )
            lines.append(
                f"Avg Iterations: [#a6e3a1]{stats.avg_iterations:.1f}[/] │ "
                f"Avg Duration: [#a6e3a1]{_fmt_duration(stats.avg_duration_s)}[/]"
            )

        observations = read_agent_observations(self.ralph_dir, agent_name)
        if observations:
            lines.append("")
            lines.append("[bold #a6adc8]Observations[/]")
            lines.append(_escape_markup(observations))

        self._show_detail("\n".join(lines))

    def _show_task_detail(self, task_id: str) -> None:
        """Show detail for a specific task."""
        task = None
        for t in self._task_memories:
            if t.task_id == task_id:
                task = t
                break

        lines = [f"[bold #cba6f7]{task_id}[/]"]
        if task:
            outcome_color = "#a6e3a1" if task.outcome == "success" else "#f38ba8"
            lines.append(
                f"Outcome: [{outcome_color}]{task.outcome}[/] │ "
                f"Duration: [#a6e3a1]{_fmt_duration(task.total_duration_s)}[/] │ "
                f"Iterations: [#a6e3a1]{task.total_iterations}[/] │ "
                f"Fix Cycles: [#a6e3a1]{task.fix_cycles}[/]"
            )
            if task.files_touched:
                lines.append(f"Files: {len(task.files_touched)} touched")

            if task.pipeline:
                lines.append("")
                lines.append("[bold #a6adc8]Pipeline[/]")
                for step, info in task.pipeline.items():
                    if isinstance(info, dict):
                        result = info.get("result", "")
                        dur = info.get("duration_s", 0)
                        lines.append(f"  {step}: {result} ({_fmt_duration(dur)})")
                    else:
                        lines.append(f"  {step}: {info}")

        analysis = read_task_analysis(self.ralph_dir, task_id)
        if analysis:
            lines.append("")
            lines.append("[bold #a6adc8]Analysis[/]")
            lines.append(_escape_markup(analysis))

        self._show_detail("\n".join(lines))

    def refresh_data(self) -> None:
        """Refresh memory data."""
        # Update header stats
        stats = read_memory_stats(self.ralph_dir)
        duration_str = _fmt_duration(stats.avg_total_duration_s) if stats.avg_total_duration_s > 0 else "-"
        header_text = (
            f"[bold]Memory[/] │ "
            f"Tasks: [#a6e3a1]{stats.tasks_analyzed}[/] │ "
            f"Success: [#a6e3a1]{stats.success_rate:.0f}%[/] │ "
            f"Avg Duration: [#a6e3a1]{duration_str}[/]"
        )
        try:
            self.query_one("#memory-stats-header", Static).update(header_text)
        except Exception:
            pass

        # Refresh agent table data
        self._agent_stats = read_all_agent_stats(self.ralph_dir)
        self._task_memories = read_all_task_memories(self.ralph_dir)

        # Update table if visible
        try:
            table = self.query_one("#memory-agent-table", DataTable)
            if table.display:
                self._populate_agent_table()
        except Exception:
            pass

    # --- Vim navigation ---

    def action_cursor_down(self) -> None:
        try:
            tree = self.query_one("#memory-tree", Tree)
            tree.action_cursor_down()
        except Exception:
            pass

    def action_cursor_up(self) -> None:
        try:
            tree = self.query_one("#memory-tree", Tree)
            tree.action_cursor_up()
        except Exception:
            pass

    def action_goto_top(self) -> None:
        try:
            tree = self.query_one("#memory-tree", Tree)
            tree.action_scroll_home()
        except Exception:
            pass

    def action_goto_bottom(self) -> None:
        try:
            tree = self.query_one("#memory-tree", Tree)
            tree.action_scroll_end()
        except Exception:
            pass


def _escape_markup(text: str) -> str:
    """Escape Rich markup characters in plain text content."""
    return text.replace("[", "\\[")
