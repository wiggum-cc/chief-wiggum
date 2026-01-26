"""Plan panel widget showing .ralph/plans/*.md files."""

from pathlib import Path
from textual.app import ComposeResult
from textual.binding import Binding
from textual.containers import Horizontal, VerticalScroll
from textual.widgets import Static, OptionList, Markdown
from textual.widgets.option_list import Option
from textual.widget import Widget


class PlanPanel(Widget):
    """Panel showing plan files with a file list on the left and content on the right."""

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
    }

    PlanPanel .plan-board {
        height: 1fr;
        width: 100%;
    }

    PlanPanel .plan-list {
        width: 30;
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
        self._selected_index: int = 0
        self._last_data_hash: str = ""

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

    def compose(self) -> ComposeResult:
        self._plan_files = self._scan_plans()

        if not self._plan_files:
            yield Static(
                "No plan files found in .ralph/plans/",
                classes="empty-message",
            )
            return

        options = [Option(f.stem, id=f.stem) for f in self._plan_files]

        with Horizontal(classes="plan-board"):
            yield OptionList(*options, id="plan-option-list", classes="plan-list")
            with VerticalScroll(classes="plan-content"):
                content = self._read_plan(self._plan_files[0])
                yield Markdown(content, id="plan-content-md")

    def on_mount(self) -> None:
        """Highlight the first item after mount."""
        if self._plan_files:
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
        """Handle plan selection from the option list."""
        if event.option_list.id != "plan-option-list":
            return
        index = event.option_index
        if 0 <= index < len(self._plan_files):
            self._selected_index = index
            try:
                md_widget = self.query_one("#plan-content-md", Markdown)
                content = self._read_plan(self._plan_files[index])
                md_widget.update(content)
            except Exception:
                pass

    def refresh_data(self) -> None:
        """Refresh plan data only if changed."""
        new_hash = self._compute_data_hash()
        if new_hash == self._last_data_hash:
            return
        self._last_data_hash = new_hash

        # Save current selection by file name (stem) before refreshing
        selected_stem = None
        if self._plan_files and 0 <= self._selected_index < len(self._plan_files):
            selected_stem = self._plan_files[self._selected_index].stem

        new_files = self._scan_plans()
        self._plan_files = new_files

        try:
            option_list = self.query_one("#plan-option-list", OptionList)
            option_list.clear_options()
            for f in self._plan_files:
                option_list.add_option(Option(f.stem, id=f.stem))
        except Exception:
            pass

        # Try to restore selection by file name, fall back to clamped index
        if selected_stem:
            new_index = next(
                (i for i, f in enumerate(self._plan_files) if f.stem == selected_stem),
                None
            )
            if new_index is not None:
                self._selected_index = new_index
            elif self._selected_index >= len(self._plan_files):
                self._selected_index = max(0, len(self._plan_files) - 1)
        elif self._selected_index >= len(self._plan_files):
            self._selected_index = max(0, len(self._plan_files) - 1)

        # Restore highlighted state and update content display
        if self._plan_files:
            try:
                option_list = self.query_one("#plan-option-list", OptionList)
                option_list.highlighted = self._selected_index
            except Exception:
                pass
            try:
                md_widget = self.query_one("#plan-content-md", Markdown)
                content = self._read_plan(self._plan_files[self._selected_index])
                md_widget.update(content)
            except Exception:
                pass

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
