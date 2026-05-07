"""Footer widget for Wiggum TUI."""

from textual.widgets import Static


class WiggumFooter(Static):
    """Custom footer showing keybinding hints."""

    DEFAULT_CSS = """
    WiggumFooter {
        background: #1e293b;
        color: #64748b;
        dock: bottom;
        height: 1;
        padding: 0 1;
    }
    """

    def render(self) -> str:
        """Render footer content."""
        bindings = [
            ("q", "Quit"),
            ("1-5", "Tabs"),
            ("s", "Stop"),
            ("k", "Kill"),
            ("r", "Refresh"),
            ("?", "Help"),
        ]
        parts = [f"[bold]{key}[/]:{action}" for key, action in bindings]
        return "  ".join(parts)
