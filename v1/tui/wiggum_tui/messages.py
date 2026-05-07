"""Shared messages for cross-widget communication."""

from textual.message import Message


class NavigateToTask(Message):
    """Message to navigate to a specific task in another tab.

    Args:
        task_id: The task ID to navigate to.
        target_tab: The tab to switch to ("plans", "conversations", etc.).
    """

    def __init__(self, task_id: str, target_tab: str) -> None:
        super().__init__()
        self.task_id = task_id
        self.target_tab = target_tab
