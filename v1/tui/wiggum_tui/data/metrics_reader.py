"""Metrics reader for metrics.json."""

import json
from pathlib import Path
from .models import Metrics, TokenUsage, CostBreakdown, ContextUsage, WorkerMetrics


def read_metrics(file_path: Path) -> Metrics:
    """Read and parse metrics.json.

    Args:
        file_path: Path to metrics.json.

    Returns:
        Metrics object with parsed data.
    """
    if not file_path.exists():
        return Metrics()

    try:
        content = file_path.read_text()
        data = json.loads(content)
    except (OSError, json.JSONDecodeError):
        return Metrics()

    # Parse summary
    summary = data.get("summary", {})

    # Parse tokens
    tokens_data = data.get("tokens", {})
    tokens = TokenUsage(
        input=tokens_data.get("input", 0),
        output=tokens_data.get("output", 0),
        cache_creation=tokens_data.get("cache_creation", 0),
        cache_read=tokens_data.get("cache_read", 0),
        total=tokens_data.get("total", 0),
    )

    # Parse cost breakdown
    cost_data = data.get("cost_breakdown", {})
    cost_breakdown = CostBreakdown(
        input=cost_data.get("input", 0.0),
        output=cost_data.get("output", 0.0),
        cache_creation=cost_data.get("cache_creation", 0.0),
        cache_read=cost_data.get("cache_read", 0.0),
        total=cost_data.get("total", 0.0),
    )

    # Parse context usage
    context_data = data.get("context", {})
    context = ContextUsage(
        tokens=context_data.get("tokens", 0),
        size=context_data.get("size", 200000),
        percent=context_data.get("percent", 0.0),
    )

    # Parse workers
    workers_data = data.get("workers", [])
    workers = []
    for w in workers_data:
        w_tokens_data = w.get("tokens", {})
        w_tokens = TokenUsage(
            input=w_tokens_data.get("input", 0),
            output=w_tokens_data.get("output", 0),
            cache_creation=w_tokens_data.get("cache_creation", 0),
            cache_read=w_tokens_data.get("cache_read", 0),
            total=w_tokens_data.get("total", 0),
        )
        w_context_data = w.get("context", {})
        w_context = ContextUsage(
            tokens=w_context_data.get("tokens", 0),
            size=w_context_data.get("size", 200000),
            percent=w_context_data.get("percent", 0.0),
        )
        workers.append(
            WorkerMetrics(
                worker_id=w.get("worker_id", ""),
                status=w.get("status", ""),
                time_spent=w.get("time_spent", "00:00:00"),
                time_seconds=w.get("time_seconds", 0),
                tokens=w_tokens,
                cost=w.get("cost", 0.0),
                pr_url=w.get("pr_url", ""),
                context=w_context,
            )
        )

    return Metrics(
        total_workers=summary.get("total_workers", 0),
        successful_workers=summary.get("successful_workers", 0),
        failed_workers=summary.get("failed_workers", 0),
        success_rate=summary.get("success_rate", 0.0),
        total_time=summary.get("total_time", "00:00:00"),
        total_time_seconds=summary.get("total_time_seconds", 0),
        total_cost=summary.get("total_cost", 0.0),
        tokens=tokens,
        cost_breakdown=cost_breakdown,
        context=context,
        workers=workers,
    )


def format_tokens(count: int) -> str:
    """Format token count for display.

    Args:
        count: Token count.

    Returns:
        Formatted string (e.g., "1.2M", "45K", "123").
    """
    if count >= 1_000_000:
        return f"{count / 1_000_000:.1f}M"
    elif count >= 1_000:
        return f"{count / 1_000:.1f}K"
    else:
        return str(count)


def format_cost(cost: float) -> str:
    """Format cost for display.

    Args:
        cost: Cost in USD.

    Returns:
        Formatted string (e.g., "$1.23").
    """
    return f"${cost:.2f}"


def format_duration(seconds: int) -> str:
    """Format duration for display.

    Args:
        seconds: Duration in seconds.

    Returns:
        Formatted string (e.g., "1h 23m", "45m 30s", "30s").
    """
    if seconds >= 3600:
        hours = seconds // 3600
        minutes = (seconds % 3600) // 60
        return f"{hours}h {minutes}m"
    elif seconds >= 60:
        minutes = seconds // 60
        secs = seconds % 60
        return f"{minutes}m {secs}s"
    else:
        return f"{seconds}s"


def format_context(percent: float) -> str:
    """Format context usage percentage for display.

    Args:
        percent: Context usage percentage (0-100).

    Returns:
        Formatted string (e.g., "45.2%").
    """
    return f"{percent:.1f}%"
