"""Plan panel widget showing .ralph/plans/*.md files."""

from pathlib import Path
from textual.app import ComposeResult
from textual.binding import Binding
from textual.containers import Horizontal, VerticalScroll
from textual.widgets import OptionList, Markdown
from textual.widgets.option_list import Option
from textual.widget import Widget

from .filter_sort_bar import FilterSortBar, SortOption
from ..data.kanban_parser import parse_kanban


class PlanPanel(Widget):
    """Panel showing plan files with a file list on the left and content on the right."""

    SORT_OPTIONS = [
        SortOption("Last Modified", "mtime"),
        SortOption("Task ID", "task_id"),
        SortOption("Title", "title"),
    ]

    BINDINGS = [
        Binding("j", "next_plan", "Next", show=False),
        Binding("k", "prev_plan", "Prev", show=False),
        Binding("g", "first_plan", "First", show=False),
        Binding("G", "last_plan", "Last", show=False),
    ]

    DEFAULT_CSS = """
    PlanPanel {
        height: 1fr;
        width: 100%;
        layout: vertical;
    }

    PlanPanel .plan-board {
        height: 1fr;
        width: 100%;
    }

    PlanPanel .plan-list {
        width: 44;
        height: 1fr;
        border: solid #45475a;
        background: #181825;
    }

    PlanPanel .plan-content {
        width: 1fr;
        height: 1fr;
        border: solid #45475a;
        background: #1e1e2e;
        padding: 1;
    }

    PlanPanel .empty-message {
        text-align: center;
        color: #7f849c;
        padding: 2;
    }
    """

    def __init__(self, ralph_dir: Path) -> None:
        super().__init__()
        self.ralph_dir = ralph_dir
        self.plans_dir = ralph_dir / "plans"
        self._plan_files: list[Path] = []
        self._filtered_plans: list[Path] = []
        self._task_titles: dict[str, str] = {}  # task_id -> title
        self._selected_index: int = 0
        self._last_data_hash: str = ""
        self._rebuilding: bool = False

    def _load_task_titles(self) -> None:
        """Parse kanban.md to build a task_id -> title map."""
        kanban_path = self.ralph_dir / "kanban.md"
        if not kanban_path.exists():
            self._task_titles = {}
            return
        tasks = parse_kanban(kanban_path)
        self._task_titles = {t.id: t.title for t in tasks}

    def _scan_plans(self) -> list[Path]:
        """Scan plans directory for .md files, sorted by mtime descending."""
        if not self.plans_dir.is_dir():
            return []
        files = list(self.plans_dir.glob("*.md"))
        files.sort(key=lambda f: f.stat().st_mtime, reverse=True)
        return files

    def _compute_data_hash(self) -> str:
        """Compute hash for change detection."""
        files = self._scan_plans()
        if not files:
            return ""
        data = [(f.name, f.stat().st_mtime) for f in files]
        return str(data)

    def _get_plan_label(self, plan_file: Path, max_width: int = 40) -> str:
        """Get display label for a plan file: 'TASK-ID: Title text...'

        Args:
            plan_file: Path to the plan .md file.
            max_width: Maximum label width.

        Returns:
            Label string.
        """
        task_id = plan_file.stem
        title = self._task_titles.get(task_id, "")
        if title:
            # Truncate to fit
            prefix = f"{task_id}: "
            remaining = max_width - len(prefix)
            if remaining > 3 and len(title) > remaining:
                title = title[: remaining - 3] + "..."
            return f"{prefix}{title}"
        return task_id

    def _apply_filter_sort(
        self,
        plans: list[Path],
        search_query: str = "",
        sort_key: str = "mtime",
        sort_ascending: bool = True,
    ) -> list[Path]:
        """Apply search and sort to plans list.

        Args:
            plans: All plan files.
            search_query: Text to search in task ID and title.
            sort_key: Sort field.
            sort_ascending: Sort direction.

        Returns:
            Filtered and sorted list.
        """
        result = list(plans)

        # Apply search
        if search_query:
            q = search_query.lower()
            result = [
                f for f in result
                if q in f.stem.lower() or q in self._task_titles.get(f.stem, "").lower()
            ]

        # Apply sort
        if sort_key == "mtime":
            result.sort(key=lambda f: f.stat().st_mtime, reverse=not sort_ascending)
        elif sort_key == "task_id":
            result.sort(key=lambda f: f.stem, reverse=not sort_ascending)
        elif sort_key == "title":
            result.sort(
                key=lambda f: self._task_titles.get(f.stem, "").lower(),
                reverse=not sort_ascending,
            )

        return result

    def compose(self) -> ComposeResult:
        self._load_task_titles()
        self._plan_files = self._scan_plans()
        self._filtered_plans = list(self._plan_files)
        self._last_data_hash = self._compute_data_hash()

        yield FilterSortBar(
            sort_options=list(self.SORT_OPTIONS),
            show_search=True,
            id="plans-filter-bar",
        )

        options = [
            Option(self._get_plan_label(f), id=f.stem)
            for f in self._filtered_plans
        ]

        initial_content = ""
        if self._filtered_plans:
            initial_content = self._read_plan(self._filtered_plans[0])
        elif not self._plan_files:
            initial_content = "*No plan files found in .ralph/plans/*"

        with Horizontal(classes="plan-board"):
            yield OptionList(*options, id="plan-option-list", classes="plan-list")
            with VerticalScroll(classes="plan-content"):
                yield Markdown(initial_content, id="plan-content-md")

    def on_mount(self) -> None:
        """Highlight the first item after mount."""
        if self._filtered_plans:
            try:
                option_list = self.query_one("#plan-option-list", OptionList)
                option_list.highlighted = 0
            except Exception:
                pass

    def _read_plan(self, path: Path) -> str:
        """Read plan file content."""
        try:
            return path.read_text()
        except Exception:
            return "(Error reading file)"

    def on_option_list_option_highlighted(self, event: OptionList.OptionHighlighted) -> None:
        """Handle plan selection from the option list.

        Ignores spurious events fired during programmatic option list rebuilds
        (clear_options + add_option cycles) which would overwrite the current
        selection with stale indices.
        """
        if event.option_list.id != "plan-option-list":
            return
        if self._rebuilding:
            return
        index = event.option_index
        if 0 <= index < len(self._filtered_plans):
            self._selected_index = index
            try:
                md_widget = self.query_one("#plan-content-md", Markdown)
                content = self._read_plan(self._filtered_plans[index])
                md_widget.update(content)
            except Exception:
                pass

    def on_filter_sort_bar_changed(self, event: FilterSortBar.Changed) -> None:
        """Handle filter/sort bar state changes."""
        self._filtered_plans = self._apply_filter_sort(
            self._plan_files,
            search_query=event.search_query,
            sort_key=event.sort_key,
            sort_ascending=event.sort_ascending,
        )
        self._rebuild_option_list()

    def _rebuild_option_list(self) -> None:
        """Rebuild the option list with current filtered plans."""
        try:
            option_list = self.query_one("#plan-option-list", OptionList)
            # Save current selection
            selected_stem = None
            if self._filtered_plans and 0 <= self._selected_index < len(self._filtered_plans):
                selected_stem = self._filtered_plans[self._selected_index].stem

            self._rebuilding = True
            option_list.clear_options()
            for f in self._filtered_plans:
                option_list.add_option(Option(self._get_plan_label(f), id=f.stem))
            self._rebuilding = False

            # Restore selection
            if selected_stem:
                new_idx = next(
                    (i for i, f in enumerate(self._filtered_plans) if f.stem == selected_stem),
                    0,
                )
                self._selected_index = new_idx
            else:
                self._selected_index = 0

            if self._filtered_plans:
                option_list.highlighted = self._selected_index
                try:
                    md_widget = self.query_one("#plan-content-md", Markdown)
                    content = self._read_plan(self._filtered_plans[self._selected_index])
                    md_widget.update(content)
                except Exception:
                    pass
        except Exception:
            self._rebuilding = False

    def refresh_data(self) -> None:
        """Refresh plan data only if changed."""
        new_hash = self._compute_data_hash()
        if new_hash == self._last_data_hash:
            return
        self._last_data_hash = new_hash

        # Save current selection by file name (stem) before refreshing
        selected_stem = None
        if self._filtered_plans and 0 <= self._selected_index < len(self._filtered_plans):
            selected_stem = self._filtered_plans[self._selected_index].stem

        self._load_task_titles()
        new_files = self._scan_plans()
        self._plan_files = new_files

        # Re-apply filter/sort
        try:
            bar = self.query_one("#plans-filter-bar", FilterSortBar)
            self._filtered_plans = self._apply_filter_sort(
                self._plan_files,
                search_query=bar.search_query,
                sort_key=bar.sort_key,
                sort_ascending=bar.sort_ascending,
            )
        except Exception:
            self._filtered_plans = list(self._plan_files)

        # Suppress OptionHighlighted events during the clear+rebuild cycle
        # so they don't overwrite _selected_index with stale indices.
        self._rebuilding = True
        try:
            option_list = self.query_one("#plan-option-list", OptionList)
            option_list.clear_options()
            for f in self._filtered_plans:
                option_list.add_option(Option(self._get_plan_label(f), id=f.stem))
        except Exception:
            pass
        finally:
            self._rebuilding = False

        # Try to restore selection by file name, fall back to clamped index
        if selected_stem:
            new_index = next(
                (i for i, f in enumerate(self._filtered_plans) if f.stem == selected_stem),
                None
            )
            if new_index is not None:
                self._selected_index = new_index
            elif self._selected_index >= len(self._filtered_plans):
                self._selected_index = max(0, len(self._filtered_plans) - 1)
        elif self._selected_index >= len(self._filtered_plans):
            self._selected_index = max(0, len(self._filtered_plans) - 1)

        # Restore highlighted state and update content display
        if self._filtered_plans:
            try:
                option_list = self.query_one("#plan-option-list", OptionList)
                option_list.highlighted = self._selected_index
            except Exception:
                pass
            try:
                md_widget = self.query_one("#plan-content-md", Markdown)
                content = self._read_plan(self._filtered_plans[self._selected_index])
                md_widget.update(content)
            except Exception:
                pass

    def select_by_task_id(self, task_id: str) -> None:
        """Select a plan by task ID.

        Args:
            task_id: Task ID to select (e.g. "TASK-001").
        """
        for i, f in enumerate(self._filtered_plans):
            if f.stem == task_id:
                self._selected_index = i
                try:
                    option_list = self.query_one("#plan-option-list", OptionList)
                    option_list.highlighted = i
                except Exception:
                    pass
                try:
                    md_widget = self.query_one("#plan-content-md", Markdown)
                    content = self._read_plan(f)
                    md_widget.update(content)
                except Exception:
                    pass
                return

    def action_next_plan(self) -> None:
        """Select next plan (vim j)."""
        try:
            option_list = self.query_one("#plan-option-list", OptionList)
            option_list.action_cursor_down()
        except Exception:
            pass

    def action_prev_plan(self) -> None:
        """Select previous plan (vim k)."""
        try:
            option_list = self.query_one("#plan-option-list", OptionList)
            option_list.action_cursor_up()
        except Exception:
            pass

    def action_first_plan(self) -> None:
        """Select first plan (vim g)."""
        try:
            option_list = self.query_one("#plan-option-list", OptionList)
            option_list.highlighted = 0
        except Exception:
            pass

    def action_last_plan(self) -> None:
        """Select last plan (vim G)."""
        try:
            option_list = self.query_one("#plan-option-list", OptionList)
            option_list.highlighted = option_list.option_count - 1
        except Exception:
            pass
