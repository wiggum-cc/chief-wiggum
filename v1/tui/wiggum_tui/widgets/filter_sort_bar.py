"""Reusable filter/sort bar widget for tables and lists."""

from __future__ import annotations

from dataclasses import dataclass
from textual.app import ComposeResult
from textual.widgets import Static, Input
from textual.widget import Widget
from textual.binding import Binding
from textual.message import Message
from textual import events


@dataclass
class SortOption:
    """A sort option with label and key."""

    label: str
    key: str


@dataclass
class FilterOption:
    """A filter option (status chip) with label, key, and active state."""

    label: str
    key: str
    active: bool = True


class _ClickableStatic(Static):
    """A Static widget that visually responds to mouse hover."""

    DEFAULT_CSS = """
    _ClickableStatic {
        width: auto;
        height: 1;
    }
    _ClickableStatic:hover {
        text-style: bold;
    }
    """


class _SortLabel(_ClickableStatic):
    """Clickable sort label - click to cycle sort field."""

    def on_click(self) -> None:
        bar = self.parent
        if isinstance(bar, FilterSortBar):
            bar.action_cycle_sort()


class _DirectionLabel(_ClickableStatic):
    """Clickable direction toggle - click to flip asc/desc."""

    def on_click(self) -> None:
        bar = self.parent
        if isinstance(bar, FilterSortBar):
            bar.action_toggle_direction()


class _FilterChip(_ClickableStatic):
    """Clickable filter chip - click to toggle this filter."""

    def __init__(self, filter_key: str, content: str = "", **kwargs) -> None:
        super().__init__(content, **kwargs)
        self.filter_key = filter_key

    def on_click(self) -> None:
        bar = self.parent
        if isinstance(bar, FilterSortBar):
            bar.toggle_filter(self.filter_key)


class _SearchHint(_ClickableStatic):
    """Clickable search hint - click to open search input."""

    def on_click(self) -> None:
        bar = self.parent
        if isinstance(bar, FilterSortBar):
            bar.action_toggle_search()


class FilterSortBar(Widget):
    """Reusable widget for sorting, filtering, and searching.

    Keybindings:
        / - Toggle search input focus
        S - Cycle sort field
        D - Toggle sort direction (asc/desc)
        Escape - Clear search and unfocus

    All elements are also clickable:
        Sort label - cycles sort field
        Direction arrow - toggles asc/desc
        Filter chips - toggles individual filters
        /search hint - opens search input

    Emits FilterSortBar.Changed when any state changes.
    """

    DEFAULT_CSS = """
    FilterSortBar {
        height: auto;
        width: 100%;
        background: #181825;
        padding: 0 1;
        layout: horizontal;
    }

    FilterSortBar .fsb-sort-info {
        width: auto;
        height: 1;
        padding: 0 1 0 0;
        color: #a6adc8;
    }

    FilterSortBar .fsb-direction {
        width: auto;
        height: 1;
        padding: 0 1 0 0;
    }

    FilterSortBar .fsb-separator {
        width: auto;
        height: 1;
        padding: 0 1 0 0;
        color: #7f849c;
    }

    FilterSortBar .fsb-chip {
        width: auto;
        height: 1;
        padding: 0 1 0 0;
    }

    FilterSortBar .fsb-search-container {
        width: auto;
        min-width: 20;
        height: 1;
    }

    FilterSortBar Input {
        width: 30;
        height: 1;
        border: none !important;
        background: #313244;
        padding: 0 1;
        display: none;
    }

    FilterSortBar Input.visible {
        display: block;
    }

    FilterSortBar .fsb-search-hint {
        width: auto;
        height: 1;
        color: #585b70;
    }
    """

    BINDINGS = [
        Binding("slash", "toggle_search", "Search /", show=True, priority=True),
        Binding("S", "cycle_sort", "Sort", show=True),
        Binding("D", "toggle_direction", "Dir", show=True),
    ]

    class Changed(Message):
        """Emitted when sort, filter, or search state changes."""

        def __init__(
            self,
            search_query: str,
            sort_key: str,
            sort_ascending: bool,
            active_filters: list[str],
        ) -> None:
            super().__init__()
            self.search_query = search_query
            self.sort_key = sort_key
            self.sort_ascending = sort_ascending
            self.active_filters = active_filters

    def __init__(
        self,
        sort_options: list[SortOption] | None = None,
        filter_options: list[FilterOption] | None = None,
        show_search: bool = True,
        id: str | None = None,
    ) -> None:
        super().__init__(id=id)
        self._sort_options = sort_options or []
        self._filter_options = filter_options or []
        self._show_search = show_search
        self._sort_index = 0
        self._sort_ascending = True
        self._search_visible = False
        self._search_query = ""

    @property
    def sort_key(self) -> str:
        """Current sort key."""
        if self._sort_options:
            return self._sort_options[self._sort_index].key
        return ""

    @property
    def sort_ascending(self) -> bool:
        """Current sort direction."""
        return self._sort_ascending

    @property
    def search_query(self) -> str:
        """Current search query."""
        return self._search_query

    @property
    def active_filters(self) -> list[str]:
        """List of active filter keys."""
        return [f.key for f in self._filter_options if f.active]

    def compose(self) -> ComposeResult:
        # Sort label (clickable to cycle sort field)
        if self._sort_options:
            opt = self._sort_options[self._sort_index]
            yield _SortLabel(
                f"[#7f849c]Sort:[/] [#89b4fa]{opt.label}[/]",
                classes="fsb-sort-info",
                id="fsb-sort-label",
            )
            # Direction arrow (clickable to toggle direction)
            direction = "▲" if self._sort_ascending else "▼"
            yield _DirectionLabel(
                f"[#89b4fa]{direction}[/]",
                classes="fsb-direction",
                id="fsb-direction",
            )

        # Filter chips (each individually clickable)
        if self._filter_options:
            yield Static("[#7f849c]│[/]", classes="fsb-separator")
            for f in self._filter_options:
                color = "#a6e3a1" if f.active else "#585b70"
                yield _FilterChip(
                    f.key,
                    f"[{color}]{f.label}[/]",
                    classes="fsb-chip",
                    id=f"fsb-chip-{f.key}",
                )

        # Search
        if self._show_search:
            yield _SearchHint(
                "[#585b70]/search[/]",
                classes="fsb-search-hint",
                id="fsb-search-hint",
            )
            yield Input(
                placeholder="Search...",
                id="fsb-search-input",
            )

    def _update_sort_label(self) -> None:
        """Update the sort label display."""
        try:
            opt = self._sort_options[self._sort_index]
            label = self.query_one("#fsb-sort-label", _SortLabel)
            label.update(f"[#7f849c]Sort:[/] [#89b4fa]{opt.label}[/]")
            direction = "▲" if self._sort_ascending else "▼"
            arrow = self.query_one("#fsb-direction", _DirectionLabel)
            arrow.update(f"[#89b4fa]{direction}[/]")
        except Exception:
            pass

    def _update_filter_chips(self) -> None:
        """Update the filter chips display."""
        for f in self._filter_options:
            try:
                chip = self.query_one(f"#fsb-chip-{f.key}", _FilterChip)
                color = "#a6e3a1" if f.active else "#585b70"
                chip.update(f"[{color}]{f.label}[/]")
            except Exception:
                pass

    def _emit_changed(self) -> None:
        """Emit Changed message with current state."""
        self.post_message(
            self.Changed(
                search_query=self._search_query,
                sort_key=self.sort_key,
                sort_ascending=self._sort_ascending,
                active_filters=self.active_filters,
            )
        )

    def action_toggle_search(self) -> None:
        """Toggle search input visibility and focus."""
        try:
            search_input = self.query_one("#fsb-search-input", Input)
            hint = self.query_one("#fsb-search-hint", _SearchHint)
            if self._search_visible:
                # Hide search
                self._search_visible = False
                search_input.remove_class("visible")
                hint.update("[#585b70]/search[/]")
                search_input.value = ""
                self._search_query = ""
                self._emit_changed()
            else:
                # Show search
                self._search_visible = True
                search_input.add_class("visible")
                hint.update("")
                search_input.focus()
        except Exception:
            pass

    def on_input_changed(self, event: Input.Changed) -> None:
        """Handle search input changes."""
        if event.input.id == "fsb-search-input":
            self._search_query = event.value
            self._emit_changed()

    def on_input_submitted(self, event: Input.Submitted) -> None:
        """Handle search input submission (Enter key)."""
        if event.input.id == "fsb-search-input":
            # Keep search active but unfocus input
            pass

    def on_key(self, event: events.Key) -> None:
        """Handle escape to clear search."""
        if event.key == "escape" and self._search_visible:
            self.action_toggle_search()
            event.stop()

    def action_cycle_sort(self) -> None:
        """Cycle to next sort option."""
        if not self._sort_options:
            return
        self._sort_index = (self._sort_index + 1) % len(self._sort_options)
        self._update_sort_label()
        self._emit_changed()

    def action_toggle_direction(self) -> None:
        """Toggle sort direction."""
        self._sort_ascending = not self._sort_ascending
        self._update_sort_label()
        self._emit_changed()

    def toggle_filter(self, key: str) -> None:
        """Toggle a filter option by key.

        Args:
            key: The filter key to toggle.
        """
        for f in self._filter_options:
            if f.key == key:
                f.active = not f.active
                break
        self._update_filter_chips()
        self._emit_changed()

    def set_filter(self, key: str, active: bool) -> None:
        """Set a filter option's active state.

        Args:
            key: The filter key.
            active: Whether the filter should be active.
        """
        for f in self._filter_options:
            if f.key == key:
                f.active = active
                break
        self._update_filter_chips()
        self._emit_changed()
