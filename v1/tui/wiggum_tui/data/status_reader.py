"""Status readers for orchestrator, API usage, costs, resume state, git state.

All readers return empty/default dataclass on file-not-found or parse error.
No exceptions propagated. mtime-based caching for frequently-read files.
"""

import json
from dataclasses import dataclass, field
from pathlib import Path


# --- Dataclasses ---

@dataclass
class ApiUsage:
    """API usage from claude-usage.json."""

    cycle_prompts: int = 0
    cycle_input_tokens: int = 0
    cycle_output_tokens: int = 0
    cycle_hours: float = 0.0
    weekly_prompts: int = 0
    weekly_input_tokens: int = 0
    weekly_output_tokens: int = 0


@dataclass
class MemoryStats:
    """Global memory stats from memory/stats.json."""

    tasks_analyzed: int = 0
    success_rate: float = 0.0
    avg_fix_cycles: float = 0.0
    avg_total_duration_s: float = 0.0


@dataclass
class CostStep:
    """A single step's cost entry."""

    step_id: str = ""
    cost: float = 0.0


@dataclass
class CostTrackerData:
    """Full cost tracker data from cost-tracker.json."""

    total_cost: float = 0.0
    steps: list[CostStep] = field(default_factory=list)


@dataclass
class ResumeAttempt:
    """A single resume attempt entry."""

    attempt: int = 0
    decision: str = ""
    reason: str = ""
    resume_from: str = ""


@dataclass
class ResumeState:
    """Resume state from resume-state.json."""

    attempt_count: int = 0
    max_attempts: int = 0
    terminal: bool = False
    history: list[ResumeAttempt] = field(default_factory=list)


@dataclass
class GitState:
    """Git state from git-state.json."""

    current_state: str = ""
    pr_number: int | None = None
    transitions: list[str] = field(default_factory=list)


# --- Caches ---

_cost_cache: dict[str, tuple[float, float | None]] = {}
_api_usage_cache: dict[str, tuple[float, ApiUsage]] = {}
_memory_stats_cache: dict[str, tuple[float, MemoryStats]] = {}


# --- Reader functions ---

def read_api_usage(ralph_dir: Path) -> ApiUsage:
    """Read API usage from .ralph/orchestrator/claude-usage.json.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        ApiUsage dataclass with token/prompt counts.
    """
    usage_path = ralph_dir / "orchestrator" / "claude-usage.json"
    cache_key = str(usage_path)

    try:
        mtime = usage_path.stat().st_mtime
    except OSError:
        return ApiUsage()

    cached = _api_usage_cache.get(cache_key)
    if cached and cached[0] == mtime:
        return cached[1]

    try:
        data = json.loads(usage_path.read_text())

        cycle = data.get("cycle", data)
        weekly = data.get("weekly", {})

        result = ApiUsage(
            cycle_prompts=cycle.get("prompts", cycle.get("prompt_count", 0)),
            cycle_input_tokens=cycle.get("input_tokens", 0),
            cycle_output_tokens=cycle.get("output_tokens", 0),
            cycle_hours=cycle.get("hours", 0.0),
            weekly_prompts=weekly.get("prompts", weekly.get("prompt_count", 0)),
            weekly_input_tokens=weekly.get("input_tokens", 0),
            weekly_output_tokens=weekly.get("output_tokens", 0),
        )
        _api_usage_cache[cache_key] = (mtime, result)
        return result
    except (json.JSONDecodeError, OSError, KeyError):
        return ApiUsage()


def read_memory_stats(ralph_dir: Path) -> MemoryStats:
    """Read global memory stats from .ralph/memory/stats.json.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        MemoryStats dataclass.
    """
    stats_path = ralph_dir / "memory" / "stats.json"
    cache_key = str(stats_path)

    try:
        mtime = stats_path.stat().st_mtime
    except OSError:
        return MemoryStats()

    cached = _memory_stats_cache.get(cache_key)
    if cached and cached[0] == mtime:
        return cached[1]

    try:
        data = json.loads(stats_path.read_text())
        result = MemoryStats(
            tasks_analyzed=data.get("tasks_analyzed", 0),
            success_rate=data.get("success_rate", 0.0),
            avg_fix_cycles=data.get("avg_fix_cycles", 0.0),
            avg_total_duration_s=data.get("avg_total_duration_s", 0.0),
        )
        _memory_stats_cache[cache_key] = (mtime, result)
        return result
    except (json.JSONDecodeError, OSError, KeyError):
        return MemoryStats()


def read_worker_cost(worker_dir: Path) -> float | None:
    """Read total cost from a worker's cost-tracker.json.

    Args:
        worker_dir: Path to worker directory.

    Returns:
        Total cost in USD, or None if not available.
    """
    cost_path = worker_dir / "cost-tracker.json"
    cache_key = str(cost_path)

    try:
        mtime = cost_path.stat().st_mtime
    except OSError:
        return None

    cached = _cost_cache.get(cache_key)
    if cached and cached[0] == mtime:
        return cached[1]

    try:
        data = json.loads(cost_path.read_text())
        total = data.get("total_cost", None)
        if total is not None:
            total = float(total)
        _cost_cache[cache_key] = (mtime, total)
        return total
    except (json.JSONDecodeError, OSError, ValueError):
        return None


def aggregate_session_cost(ralph_dir: Path) -> float:
    """Sum total costs from all workers' cost-tracker.json files.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        Total session cost in USD.
    """
    total = 0.0

    for search_dir in [ralph_dir / "workers", ralph_dir / "history"]:
        if not search_dir.is_dir():
            continue
        try:
            for entry in search_dir.iterdir():
                if entry.name.startswith("worker-") and entry.is_dir():
                    cost = read_worker_cost(entry)
                    if cost is not None:
                        total += cost
        except OSError:
            continue

    return total


def read_cost_tracker(worker_dir: Path) -> CostTrackerData:
    """Read full cost tracker data from a worker's cost-tracker.json.

    Args:
        worker_dir: Path to worker directory.

    Returns:
        CostTrackerData with total and per-step breakdown.
    """
    cost_path = worker_dir / "cost-tracker.json"

    try:
        data = json.loads(cost_path.read_text())
    except (json.JSONDecodeError, OSError):
        return CostTrackerData()

    total = float(data.get("total_cost", 0.0))
    steps = []

    # Parse per-step costs
    step_costs = data.get("steps", data.get("step_costs", {}))
    if isinstance(step_costs, dict):
        for step_id, cost_val in step_costs.items():
            if isinstance(cost_val, dict):
                cost_val = cost_val.get("cost", cost_val.get("total_cost", 0.0))
            steps.append(CostStep(step_id=step_id, cost=float(cost_val)))
    elif isinstance(step_costs, list):
        for entry in step_costs:
            if isinstance(entry, dict):
                steps.append(CostStep(
                    step_id=entry.get("step_id", entry.get("id", "")),
                    cost=float(entry.get("cost", entry.get("total_cost", 0.0))),
                ))

    return CostTrackerData(total_cost=total, steps=steps)


def read_resume_state(worker_dir: Path) -> ResumeState:
    """Read resume state from a worker's resume-state.json.

    Args:
        worker_dir: Path to worker directory.

    Returns:
        ResumeState with attempt history.
    """
    state_path = worker_dir / "resume-state.json"

    try:
        data = json.loads(state_path.read_text())
    except (json.JSONDecodeError, OSError):
        return ResumeState()

    history = []
    for entry in data.get("history", []):
        if isinstance(entry, dict):
            history.append(ResumeAttempt(
                attempt=entry.get("attempt", 0),
                decision=entry.get("decision", ""),
                reason=entry.get("reason", ""),
                resume_from=entry.get("resume_from", entry.get("step", "")),
            ))

    return ResumeState(
        attempt_count=data.get("attempt_count", data.get("attempts", 0)),
        max_attempts=data.get("max_attempts", 0),
        terminal=data.get("terminal", False),
        history=history,
    )


def read_git_state(worker_dir: Path) -> GitState:
    """Read git state from a worker's git-state.json.

    Args:
        worker_dir: Path to worker directory.

    Returns:
        GitState with current state, PR number, and transition history.
    """
    state_path = worker_dir / "git-state.json"

    try:
        data = json.loads(state_path.read_text())
    except (json.JSONDecodeError, OSError):
        return GitState()

    transitions = []
    for entry in data.get("transitions", data.get("history", [])):
        if isinstance(entry, str):
            transitions.append(entry)
        elif isinstance(entry, dict):
            transitions.append(entry.get("to", entry.get("state", "")))

    return GitState(
        current_state=data.get("current_state", ""),
        pr_number=data.get("pr_number", data.get("pr", None)),
        transitions=transitions,
    )


def read_pipeline_steps_ordered(worker_dir: Path) -> list[str]:
    """Read ordered pipeline step list from a worker's pipeline config.

    Args:
        worker_dir: Path to worker directory.

    Returns:
        Ordered list of step IDs. Falls back to steps dict keys.
    """
    # Try pipeline.source for ordered list
    source_path = worker_dir / "pipeline.source"
    if source_path.exists():
        try:
            data = json.loads(source_path.read_text())
            if isinstance(data, list):
                return data
            ordered = data.get("steps_ordered", data.get("order", []))
            if ordered:
                return ordered
        except (json.JSONDecodeError, OSError):
            pass

    # Fall back to pipeline-config.json
    config_path = worker_dir / "pipeline-config.json"
    try:
        data = json.loads(config_path.read_text())
        # Try ordered_steps first
        ordered = data.get("ordered_steps", data.get("step_order", []))
        if ordered:
            return ordered
        # Fall back to steps dict keys
        steps = data.get("steps", {})
        if isinstance(steps, dict):
            return list(steps.keys())
    except (json.JSONDecodeError, OSError):
        pass

    return []
