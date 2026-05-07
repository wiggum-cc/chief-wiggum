"""Shared utilities for wiggum TUI."""

import time


def format_relative_time(epoch: int) -> str:
    """Format an epoch timestamp as a human-readable relative time string.

    Args:
        epoch: Unix timestamp in seconds.

    Returns:
        String like "5 seconds ago", "3 minutes ago", "2 hours ago", "1 day ago",
        or ISO date string if >7 days ago.
    """
    now = int(time.time())
    diff = now - epoch

    if diff < 0:
        return "just now"

    if diff < 60:
        unit = "second" if diff == 1 else "seconds"
        return f"{diff} {unit} ago"

    minutes = diff // 60
    if minutes < 60:
        unit = "minute" if minutes == 1 else "minutes"
        return f"{minutes} {unit} ago"

    hours = diff // 3600
    if hours < 24:
        unit = "hour" if hours == 1 else "hours"
        return f"{hours} {unit} ago"

    days = diff // 86400
    if days <= 7:
        unit = "day" if days == 1 else "days"
        return f"{days} {unit} ago"

    # More than 7 days: show ISO date
    import datetime
    dt = datetime.datetime.fromtimestamp(epoch)
    return dt.strftime("%Y-%m-%d %H:%M")
