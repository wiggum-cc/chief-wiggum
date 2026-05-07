"""Pytest configuration and fixtures for TUI tests."""

import pytest
from pathlib import Path


@pytest.fixture
def fixtures_dir() -> Path:
    """Return the fixtures directory path."""
    return Path(__file__).parent / "fixtures"


@pytest.fixture
def ralph_empty(fixtures_dir: Path) -> Path:
    """Return path to empty ralph directory fixture."""
    return fixtures_dir / "ralph-empty"


@pytest.fixture
def ralph_with_workers(fixtures_dir: Path) -> Path:
    """Return path to ralph directory with workers fixture."""
    return fixtures_dir / "ralph-with-workers"


@pytest.fixture
def tmp_ralph(tmp_path: Path) -> Path:
    """Create a temporary ralph directory for testing.

    Returns the path to the .ralph directory.
    """
    ralph_dir = tmp_path / ".ralph"
    ralph_dir.mkdir()
    (ralph_dir / "workers").mkdir()
    (ralph_dir / "logs").mkdir()
    (ralph_dir / "plans").mkdir()
    return ralph_dir


@pytest.fixture
def sample_kanban_content() -> str:
    """Return sample kanban.md content for testing."""
    return """# Kanban Board

## Pending
- [ ] **[TASK-001]** Implement feature A
  - Description: Add new feature A to the system
  - Priority: HIGH
  - Dependencies: none

## In Progress
- [=] **[TASK-002]** Fix bug in parser
  - Description: Parser fails on edge cases
  - Priority: CRITICAL
  - Dependencies: none

## Pending Approval
- [P] **[TASK-003]** Update documentation
  - Description: Docs need refresh
  - Priority: LOW
  - Dependencies: TASK-001

## Complete
- [x] **[TASK-004]** Setup CI pipeline
  - Description: Configure GitHub Actions
  - Priority: MEDIUM
  - Dependencies: none

## Failed
- [*] **[TASK-005]** Legacy migration
  - Description: Migration script failed
  - Priority: HIGH
  - Dependencies: TASK-004
"""


@pytest.fixture
def sample_log_content() -> str:
    """Return sample log file content for testing."""
    return """[2024-01-15 10:00:00] INFO: Starting worker for TASK-001
[2024-01-15 10:00:01] DEBUG: Loading configuration
[2024-01-15 10:00:02] INFO: Executing plan-mode agent
[2024-01-15 10:00:10] WARN: Rate limit approaching
[2024-01-15 10:00:15] ERROR: API call failed, retrying
[2024-01-15 10:00:20] INFO: Retry successful
"""


@pytest.fixture
def sample_metrics_data() -> dict:
    """Return sample metrics.json data for testing."""
    return {
        "summary": {
            "total_workers": 5,
            "successful_workers": 3,
            "failed_workers": 1,
            "success_rate": 75.0,
            "total_time": "01:23:45",
            "total_time_seconds": 5025,
            "total_cost": 2.50,
        },
        "tokens": {
            "input": 150000,
            "output": 50000,
            "cache_creation": 10000,
            "cache_read": 80000,
            "total": 290000,
        },
        "cost_breakdown": {
            "input": 1.50,
            "output": 0.75,
            "cache_creation": 0.15,
            "cache_read": 0.10,
            "total": 2.50,
        },
        "context": {
            "tokens": 45000,
            "size": 200000,
            "percent": 22.5,
        },
        "workers": [
            {
                "worker_id": "worker-TEST-001-1700000000",
                "status": "success",
                "time_spent": "00:15:30",
                "time_seconds": 930,
                "tokens": {
                    "input": 30000,
                    "output": 10000,
                    "cache_creation": 2000,
                    "cache_read": 16000,
                    "total": 58000,
                },
                "cost": 0.50,
                "pr_url": "https://github.com/example/repo/pull/123",
                "context": {
                    "tokens": 9000,
                    "size": 200000,
                    "percent": 4.5,
                },
            }
        ],
    }


@pytest.fixture
def sample_iteration_log_entries() -> list[dict]:
    """Return sample iteration log NDJSON entries for testing."""
    return [
        {
            "type": "iteration_start",
            "iteration": 0,
            "timestamp": "2024-01-15T10:00:00Z",
            "system_prompt": "You are a helpful assistant.",
            "user_prompt": "Fix the bug in parser.py",
        },
        {
            "type": "assistant",
            "timestamp": "2024-01-15T10:00:05Z",
            "message": {
                "content": [
                    {"type": "text", "text": "I'll analyze the parser.py file."},
                    {
                        "type": "tool_use",
                        "id": "tool_001",
                        "name": "Read",
                        "input": {"file_path": "/path/to/parser.py"},
                    },
                ]
            },
        },
        {
            "type": "user",
            "timestamp": "2024-01-15T10:00:06Z",
            "tool_use_result": {"type": "text", "content": "file content here..."},
            "message": {
                "content": [
                    {
                        "type": "tool_result",
                        "tool_use_id": "tool_001",
                        "content": "file content here...",
                    }
                ]
            },
        },
        {
            "type": "result",
            "iteration": 0,
            "subtype": "success",
            "duration_ms": 15000,
            "duration_api_ms": 12000,
            "num_turns": 5,
            "total_cost_usd": 0.25,
            "is_error": False,
            "usage": {
                "input_tokens": 5000,
                "output_tokens": 1500,
                "cache_creation_input_tokens": 500,
                "cache_read_input_tokens": 3000,
            },
        },
    ]
