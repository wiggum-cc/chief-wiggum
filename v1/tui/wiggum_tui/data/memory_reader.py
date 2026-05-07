"""Readers for the memory system (.ralph/memory/).

Provides access to agent performance stats, task analysis,
learned patterns, and escalated issues.
"""

import json
from dataclasses import dataclass, field
from pathlib import Path


# --- Dataclasses ---

@dataclass
class AgentStats:
    """Per-agent stats from memory/agents/{name}/stats.json."""

    agent_type: str = ""
    runs: int = 0
    pass_rate: float = 0.0
    fix_rate: float = 0.0
    fail_rate: float = 0.0
    avg_iterations: float = 0.0
    avg_duration_s: float = 0.0


@dataclass
class TaskMemory:
    """Per-task memory from memory/tasks/{id}/stats.json."""

    task_id: str = ""
    outcome: str = ""
    total_duration_s: float = 0.0
    total_iterations: int = 0
    fix_cycles: int = 0
    pipeline: dict = field(default_factory=dict)
    files_touched: list[str] = field(default_factory=list)


@dataclass
class PatternEntry:
    """A learned pattern file."""

    category: str = ""
    name: str = ""
    file_path: str = ""


@dataclass
class EscalatedIssues:
    """Escalated issues requiring human intervention."""

    open_count: int = 0
    content: str = ""


# --- Reader functions ---

def read_all_agent_stats(ralph_dir: Path) -> list[AgentStats]:
    """Scan memory/agents/*/stats.json and return all agent stats.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        List of AgentStats sorted by pass_rate ascending (worst first).
    """
    agents_dir = ralph_dir / "memory" / "agents"
    if not agents_dir.is_dir():
        return []

    results = []
    try:
        for entry in agents_dir.iterdir():
            if not entry.is_dir():
                continue
            stats_path = entry / "stats.json"
            if not stats_path.exists():
                continue
            try:
                data = json.loads(stats_path.read_text())
                results.append(AgentStats(
                    agent_type=entry.name,
                    runs=data.get("runs", 0),
                    pass_rate=data.get("pass_rate", 0.0),
                    fix_rate=data.get("fix_rate", 0.0),
                    fail_rate=data.get("fail_rate", 0.0),
                    avg_iterations=data.get("avg_iterations", 0.0),
                    avg_duration_s=data.get("avg_duration_s", 0.0),
                ))
            except (json.JSONDecodeError, OSError):
                continue
    except OSError:
        pass

    results.sort(key=lambda a: a.pass_rate)
    return results


def read_agent_observations(ralph_dir: Path, agent: str) -> str:
    """Read observations.md for a specific agent.

    Args:
        ralph_dir: Path to .ralph directory.
        agent: Agent name.

    Returns:
        Raw markdown content, or empty string.
    """
    obs_path = ralph_dir / "memory" / "agents" / agent / "observations.md"
    try:
        return obs_path.read_text()
    except (OSError, FileNotFoundError):
        return ""


def read_all_task_memories(ralph_dir: Path) -> list[TaskMemory]:
    """Scan memory/tasks/*/stats.json and return all task memories.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        List of TaskMemory sorted by task_id.
    """
    tasks_dir = ralph_dir / "memory" / "tasks"
    if not tasks_dir.is_dir():
        return []

    results = []
    try:
        for entry in tasks_dir.iterdir():
            if not entry.is_dir():
                continue
            stats_path = entry / "stats.json"
            if not stats_path.exists():
                continue
            try:
                data = json.loads(stats_path.read_text())
                results.append(TaskMemory(
                    task_id=entry.name,
                    outcome=data.get("outcome", ""),
                    total_duration_s=data.get("total_duration_s", 0.0),
                    total_iterations=data.get("total_iterations", 0),
                    fix_cycles=data.get("fix_cycles", 0),
                    pipeline=data.get("pipeline", {}),
                    files_touched=data.get("files_touched", []),
                ))
            except (json.JSONDecodeError, OSError):
                continue
    except OSError:
        pass

    results.sort(key=lambda t: t.task_id)
    return results


def read_task_analysis(ralph_dir: Path, task_id: str) -> str:
    """Read analysis.md for a specific task.

    Args:
        ralph_dir: Path to .ralph directory.
        task_id: Task ID.

    Returns:
        Raw markdown content, or empty string.
    """
    analysis_path = ralph_dir / "memory" / "tasks" / task_id / "analysis.md"
    try:
        return analysis_path.read_text()
    except (OSError, FileNotFoundError):
        return ""


def read_pattern_tree(ralph_dir: Path) -> dict[str, list[PatternEntry]]:
    """Scan memory/patterns/ for pattern categories and entries.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        Dict mapping category name to list of PatternEntry.
    """
    patterns_dir = ralph_dir / "memory" / "patterns"
    if not patterns_dir.is_dir():
        return {}

    tree: dict[str, list[PatternEntry]] = {}
    try:
        for category_dir in sorted(patterns_dir.iterdir()):
            if not category_dir.is_dir():
                continue
            category = category_dir.name
            entries = []
            for md_file in sorted(category_dir.glob("*.md")):
                if md_file.name == "INDEX.md":
                    continue
                entries.append(PatternEntry(
                    category=category,
                    name=md_file.stem,
                    file_path=str(md_file),
                ))
            if entries:
                tree[category] = entries
    except OSError:
        pass

    return tree


def read_pattern_content(path: str) -> str:
    """Read a pattern markdown file.

    Args:
        path: Path to the pattern .md file.

    Returns:
        Raw markdown content, or empty string.
    """
    try:
        return Path(path).read_text()
    except (OSError, FileNotFoundError):
        return ""


def read_escalated(ralph_dir: Path) -> EscalatedIssues:
    """Read ESCALATED.md from memory directory.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        EscalatedIssues with content and open count.
    """
    escalated_path = ralph_dir / "memory" / "ESCALATED.md"
    try:
        content = escalated_path.read_text()
        # Count open issues (lines starting with "- [ ]" or "## ")
        open_count = sum(
            1 for line in content.splitlines()
            if line.strip().startswith("- [ ]") or line.strip().startswith("- [!")
        )
        return EscalatedIssues(open_count=open_count, content=content)
    except (OSError, FileNotFoundError):
        return EscalatedIssues()
