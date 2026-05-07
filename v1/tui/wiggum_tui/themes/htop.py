"""Catppuccin Mocha color scheme for wiggum TUI."""

# Catppuccin Mocha Palette
CATPPUCCIN = {
    # Base colors
    "rosewater": "#f5e0dc",
    "flamingo": "#f2cdcd",
    "pink": "#f5c2e7",
    "mauve": "#cba6f7",
    "red": "#f38ba8",
    "maroon": "#eba0ac",
    "peach": "#fab387",
    "yellow": "#f9e2af",
    "green": "#a6e3a1",
    "teal": "#94e2d5",
    "sky": "#89dceb",
    "sapphire": "#74c7ec",
    "blue": "#89b4fa",
    "lavender": "#b4befe",
    # Surface & background
    "text": "#cdd6f4",
    "subtext1": "#bac2de",
    "subtext0": "#a6adc8",
    "overlay2": "#9399b2",
    "overlay1": "#7f849c",
    "overlay0": "#6c7086",
    "surface2": "#585b70",
    "surface1": "#45475a",
    "surface0": "#313244",
    "base": "#1e1e2e",
    "mantle": "#181825",
    "crust": "#11111b",
}

COLORS = {
    # Status colors
    "running": CATPPUCCIN["green"],
    "stopped": CATPPUCCIN["overlay1"],
    "completed": CATPPUCCIN["blue"],
    "failed": CATPPUCCIN["red"],
    "pending": CATPPUCCIN["subtext0"],
    "in_progress": CATPPUCCIN["peach"],
    # Log levels
    "debug": CATPPUCCIN["overlay1"],
    "info": CATPPUCCIN["blue"],
    "warn": CATPPUCCIN["yellow"],
    "error": CATPPUCCIN["red"],
    # Priority
    "critical": CATPPUCCIN["red"],
    "high": CATPPUCCIN["peach"],
    "medium": CATPPUCCIN["blue"],
    "low": CATPPUCCIN["overlay1"],
    # UI elements
    "header_bg": CATPPUCCIN["mantle"],
    "panel_bg": CATPPUCCIN["base"],
    "border": CATPPUCCIN["surface1"],
    "text": CATPPUCCIN["text"],
    "muted": CATPPUCCIN["overlay1"],
    "accent": CATPPUCCIN["mauve"],
    "selected": CATPPUCCIN["surface1"],
}

# Textual CSS theme
HTOP_THEME = f"""
Screen {{
    background: {CATPPUCCIN["base"]};
}}

Header {{
    background: {CATPPUCCIN["mantle"]};
    color: {CATPPUCCIN["text"]};
    dock: top;
    height: 1;
}}

Footer {{
    background: {CATPPUCCIN["mantle"]};
    color: {CATPPUCCIN["overlay1"]};
    dock: bottom;
    height: 1;
}}

.panel {{
    background: {CATPPUCCIN["base"]};
    border: solid {CATPPUCCIN["surface1"]};
}}

.panel-title {{
    background: {CATPPUCCIN["mantle"]};
    color: {CATPPUCCIN["mauve"]};
    text-style: bold;
}}

DataTable {{
    background: {CATPPUCCIN["base"]};
}}

DataTable > .datatable--header {{
    background: {CATPPUCCIN["mantle"]};
    color: {CATPPUCCIN["text"]};
    text-style: bold;
}}

DataTable > .datatable--cursor {{
    background: {CATPPUCCIN["surface1"]};
    color: {CATPPUCCIN["text"]};
}}

.status-running {{
    color: {CATPPUCCIN["green"]};
}}

.status-stopped {{
    color: {CATPPUCCIN["overlay1"]};
}}

.status-completed {{
    color: {CATPPUCCIN["blue"]};
}}

.status-failed {{
    color: {CATPPUCCIN["red"]};
}}

.status-merged {{
    color: {CATPPUCCIN["overlay0"]};
}}

.status-pending {{
    color: {CATPPUCCIN["subtext0"]};
}}

.status-in_progress {{
    color: {CATPPUCCIN["peach"]};
}}

.log-debug {{
    color: {CATPPUCCIN["overlay1"]};
}}

.log-info {{
    color: {CATPPUCCIN["blue"]};
}}

.log-warn {{
    color: {CATPPUCCIN["yellow"]};
}}

.log-error {{
    color: {CATPPUCCIN["red"]};
}}

.priority-critical {{
    color: {CATPPUCCIN["red"]};
    text-style: bold;
}}

.priority-high {{
    color: {CATPPUCCIN["peach"]};
}}

.priority-medium {{
    color: {CATPPUCCIN["blue"]};
}}

.priority-low {{
    color: {CATPPUCCIN["overlay1"]};
}}

TabbedContent {{
    background: {CATPPUCCIN["base"]};
    height: 1fr;
}}

TabPane {{
    background: {CATPPUCCIN["base"]};
    padding: 0;
    height: 1fr;
}}

ContentSwitcher {{
    height: 1fr;
}}

Tabs {{
    background: {CATPPUCCIN["mantle"]};
}}

Tab {{
    background: {CATPPUCCIN["mantle"]};
    color: {CATPPUCCIN["overlay1"]};
}}

Tab.-active {{
    background: {CATPPUCCIN["base"]};
    color: {CATPPUCCIN["mauve"]};
    text-style: bold;
}}

RichLog {{
    background: {CATPPUCCIN["base"]};
    scrollbar-background: {CATPPUCCIN["mantle"]};
    scrollbar-color: {CATPPUCCIN["surface1"]};
}}

Tree {{
    background: {CATPPUCCIN["base"]};
}}

Tree > .tree--cursor {{
    background: {CATPPUCCIN["surface1"]};
}}

Select {{
    background: {CATPPUCCIN["mantle"]};
    border: solid {CATPPUCCIN["surface1"]};
}}

SelectCurrent {{
    background: {CATPPUCCIN["mantle"]};
    padding: 0;
}}

SelectOverlay {{
    background: {CATPPUCCIN["mantle"]};
    border: solid {CATPPUCCIN["surface1"]};
}}

OptionList {{
    background: {CATPPUCCIN["mantle"]};
    padding: 0;
}}

OptionList > .option-list--option {{
    padding: 0 1;
}}

OptionList > .option-list--option-highlighted {{
    background: {CATPPUCCIN["surface1"]};
}}

.metric-card {{
    background: {CATPPUCCIN["mantle"]};
    border: solid {CATPPUCCIN["surface1"]};
    padding: 1;
    margin: 1;
}}

.metric-value {{
    color: {CATPPUCCIN["green"]};
    text-style: bold;
}}

.metric-label {{
    color: {CATPPUCCIN["overlay1"]};
}}

.kanban-column {{
    width: 1fr;
    height: 100%;
    border: solid {CATPPUCCIN["surface1"]};
}}

.kanban-header {{
    background: {CATPPUCCIN["mantle"]};
    color: {CATPPUCCIN["text"]};
    text-align: center;
    text-style: bold;
    height: 1;
}}

.kanban-task {{
    background: {CATPPUCCIN["mantle"]};
    border: solid {CATPPUCCIN["surface1"]};
    margin: 0 1;
    padding: 0 1;
    height: auto;
}}

/* Memory Panel */
MemoryPanel .memory-header {{
    height: 1;
    background: {CATPPUCCIN["mantle"]};
    padding: 0 1;
}}

MemoryPanel .memory-body {{
    height: 1fr;
    width: 100%;
}}

MemoryPanel #memory-tree {{
    width: 25;
    min-width: 20;
    max-width: 35;
    height: 1fr;
    border-right: solid {CATPPUCCIN["surface1"]};
    background: {CATPPUCCIN["base"]};
}}

MemoryPanel #memory-content {{
    width: 1fr;
    height: 1fr;
    padding: 0 1;
}}

MemoryPanel #memory-agent-table {{
    height: 1fr;
}}

MemoryPanel #memory-detail {{
    height: 1fr;
    padding: 0 1;
}}
"""
