"""Tests for kanban_parser module."""

from pathlib import Path

from wiggum_tui.data.kanban_parser import (
    parse_kanban,
    group_tasks_by_status,
    get_task_counts,
    STATUS_MAP,
    TASK_PATTERN,
)
from wiggum_tui.data.models import Task, TaskStatus


class TestTaskPattern:
    """Tests for the task regex pattern."""

    def test_matches_pending_task(self):
        line = "- [ ] **[TASK-001]** Fix the bug"
        match = TASK_PATTERN.match(line)
        assert match is not None
        status_char, task_id, title = match.groups()
        assert status_char == " "
        assert task_id == "TASK-001"
        assert title == "Fix the bug"

    def test_matches_in_progress_task(self):
        line = "- [=] **[DEV-42]** Implement feature"
        match = TASK_PATTERN.match(line)
        assert match is not None
        status_char, task_id, title = match.groups()
        assert status_char == "="
        assert task_id == "DEV-42"

    def test_matches_complete_task(self):
        line = "- [x] **[TEST-1]** Done"
        match = TASK_PATTERN.match(line)
        assert match is not None
        status_char, task_id, title = match.groups()
        assert status_char == "x"
        assert task_id == "TEST-1"

    def test_matches_failed_task(self):
        line = "- [*] **[FAIL-999]** Crashed"
        match = TASK_PATTERN.match(line)
        assert match is not None
        assert match.group(1) == "*"

    def test_matches_not_planned_task(self):
        line = "- [N] **[SKIP-01]** Won't do"
        match = TASK_PATTERN.match(line)
        assert match is not None
        assert match.group(1) == "N"

    def test_matches_pending_approval_task(self):
        line = "- [P] **[PR-123]** Awaiting review"
        match = TASK_PATTERN.match(line)
        assert match is not None
        assert match.group(1) == "P"

    def test_matches_timeout_task(self):
        line = "- [T] **[SLOW-01]** Timed out"
        match = TASK_PATTERN.match(line)
        assert match is not None
        assert match.group(1) == "T"

    def test_no_match_invalid_format(self):
        invalid_lines = [
            "- [ ] [TASK-001] Missing bold markers",
            "- [ ] **TASK-001** Missing brackets",
            "[ ] **[TASK-001]** Missing dash",
            "  - [ ] **[TASK-001]** Indented",
            "- [X] **[TASK-001]** Wrong case",
        ]
        for line in invalid_lines:
            assert TASK_PATTERN.match(line) is None, f"Should not match: {line}"

    def test_task_id_constraints(self):
        # Valid task IDs: 2-10 letter prefix, 1-4 digit number
        valid_ids = ["AB-1", "ABCDEFGHIJ-9999", "TEST-001", "dev-42"]
        for task_id in valid_ids:
            line = f"- [ ] **[{task_id}]** Title"
            match = TASK_PATTERN.match(line)
            assert match is not None, f"Should match: {task_id}"

        # Invalid task IDs
        invalid_ids = ["A-1", "ABCDEFGHIJK-1", "TEST-12345", "123-ABC"]
        for task_id in invalid_ids:
            line = f"- [ ] **[{task_id}]** Title"
            match = TASK_PATTERN.match(line)
            assert match is None, f"Should not match: {task_id}"


class TestStatusMap:
    """Tests for status mapping."""

    def test_all_statuses_mapped(self):
        expected_statuses = {
            "[ ]": TaskStatus.PENDING,
            "[=]": TaskStatus.IN_PROGRESS,
            "[P]": TaskStatus.PENDING_APPROVAL,
            "[x]": TaskStatus.COMPLETE,
            "[N]": TaskStatus.NOT_PLANNED,
            "[*]": TaskStatus.FAILED,
            "[T]": TaskStatus.FAILED,  # Timeout maps to failed
        }
        for marker, expected in expected_statuses.items():
            assert STATUS_MAP[marker] == expected


class TestParseKanban:
    """Tests for parse_kanban function."""

    def test_empty_file(self, tmp_path: Path):
        kanban = tmp_path / "kanban.md"
        kanban.write_text("")
        tasks = parse_kanban(kanban)
        assert tasks == []

    def test_no_tasks(self, tmp_path: Path):
        kanban = tmp_path / "kanban.md"
        kanban.write_text("# Kanban\n\n## Pending\n\n## Complete\n")
        tasks = parse_kanban(kanban)
        assert tasks == []

    def test_file_not_found(self, tmp_path: Path):
        kanban = tmp_path / "nonexistent.md"
        tasks = parse_kanban(kanban)
        assert tasks == []

    def test_single_task(self, tmp_path: Path):
        kanban = tmp_path / "kanban.md"
        kanban.write_text("- [ ] **[TASK-001]** Do something\n")
        tasks = parse_kanban(kanban)
        assert len(tasks) == 1
        assert tasks[0].id == "TASK-001"
        assert tasks[0].title == "Do something"
        assert tasks[0].status == TaskStatus.PENDING

    def test_multiple_tasks_different_statuses(self, tmp_path: Path):
        content = """# Kanban

- [ ] **[TASK-001]** Pending task
- [=] **[TASK-002]** In progress
- [x] **[TASK-003]** Complete
- [*] **[TASK-004]** Failed
"""
        kanban = tmp_path / "kanban.md"
        kanban.write_text(content)
        tasks = parse_kanban(kanban)

        assert len(tasks) == 4
        assert tasks[0].status == TaskStatus.PENDING
        assert tasks[1].status == TaskStatus.IN_PROGRESS
        assert tasks[2].status == TaskStatus.COMPLETE
        assert tasks[3].status == TaskStatus.FAILED

    def test_parses_description(self, tmp_path: Path):
        content = """- [ ] **[TASK-001]** Task title
  - Description: This is the description
  - Priority: HIGH
  - Dependencies: none
"""
        kanban = tmp_path / "kanban.md"
        kanban.write_text(content)
        tasks = parse_kanban(kanban)

        assert len(tasks) == 1
        assert tasks[0].description == "This is the description"

    def test_parses_priority(self, tmp_path: Path):
        content = """- [ ] **[TASK-001]** Critical task
  - Priority: CRITICAL
  - Dependencies: none

- [ ] **[TASK-002]** High priority
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-003]** Medium priority
  - Priority: MEDIUM
  - Dependencies: none

- [ ] **[TASK-004]** Low priority
  - Priority: LOW
  - Dependencies: none
"""
        kanban = tmp_path / "kanban.md"
        kanban.write_text(content)
        tasks = parse_kanban(kanban)

        assert tasks[0].priority == "CRITICAL"
        assert tasks[1].priority == "HIGH"
        assert tasks[2].priority == "MEDIUM"
        assert tasks[3].priority == "LOW"

    def test_parses_dependencies(self, tmp_path: Path):
        content = """- [ ] **[TASK-001]** No deps
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-002]** Single dep
  - Priority: HIGH
  - Dependencies: TASK-001

- [ ] **[TASK-003]** Multiple deps
  - Priority: HIGH
  - Dependencies: TASK-001, TASK-002
"""
        kanban = tmp_path / "kanban.md"
        kanban.write_text(content)
        tasks = parse_kanban(kanban)

        assert tasks[0].dependencies == []
        assert tasks[1].dependencies == ["TASK-001"]
        assert tasks[2].dependencies == ["TASK-001", "TASK-002"]

    def test_parses_scope_list(self, tmp_path: Path):
        content = """- [ ] **[TASK-001]** Task with scope
  - Priority: HIGH
  - Dependencies: none
  - Scope:
    - Item one
    - Item two
    - Item three
"""
        kanban = tmp_path / "kanban.md"
        kanban.write_text(content)
        tasks = parse_kanban(kanban)

        assert len(tasks) == 1
        assert tasks[0].scope == ["Item one", "Item two", "Item three"]

    def test_parses_acceptance_criteria(self, tmp_path: Path):
        content = """- [ ] **[TASK-001]** Task with AC
  - Priority: HIGH
  - Dependencies: none
  - Acceptance Criteria:
    - Tests pass
    - Code reviewed
"""
        kanban = tmp_path / "kanban.md"
        kanban.write_text(content)
        tasks = parse_kanban(kanban)

        assert tasks[0].acceptance_criteria == ["Tests pass", "Code reviewed"]

    def test_parses_complexity(self, tmp_path: Path):
        content = """- [ ] **[TASK-001]** High complexity
  - Priority: HIGH
  - Complexity: HIGH
  - Dependencies: none
"""
        kanban = tmp_path / "kanban.md"
        kanban.write_text(content)
        tasks = parse_kanban(kanban)

        assert tasks[0].complexity == "HIGH"

    def test_fixture_ralph_empty(self, ralph_empty: Path):
        kanban = ralph_empty / "kanban.md"
        tasks = parse_kanban(kanban)
        assert tasks == []

    def test_fixture_ralph_with_workers(self, ralph_with_workers: Path):
        kanban = ralph_with_workers / "kanban.md"
        tasks = parse_kanban(kanban)
        assert len(tasks) == 4

        # Check specific tasks
        task_ids = {t.id for t in tasks}
        assert task_ids == {"TEST-001", "TEST-002", "TEST-003", "TEST-004"}

        # Check statuses
        by_id = {t.id: t for t in tasks}
        assert by_id["TEST-001"].status == TaskStatus.IN_PROGRESS
        assert by_id["TEST-002"].status == TaskStatus.PENDING
        assert by_id["TEST-003"].status == TaskStatus.COMPLETE
        assert by_id["TEST-004"].status == TaskStatus.FAILED


class TestGroupTasksByStatus:
    """Tests for group_tasks_by_status function."""

    def test_empty_list(self):
        result = group_tasks_by_status([])
        assert result[TaskStatus.PENDING] == []
        assert result[TaskStatus.IN_PROGRESS] == []
        assert result[TaskStatus.COMPLETE] == []

    def test_groups_correctly(self):
        tasks = [
            Task(id="T-1", title="A", status=TaskStatus.PENDING),
            Task(id="T-2", title="B", status=TaskStatus.PENDING),
            Task(id="T-3", title="C", status=TaskStatus.IN_PROGRESS),
            Task(id="T-4", title="D", status=TaskStatus.COMPLETE),
        ]
        result = group_tasks_by_status(tasks)

        assert len(result[TaskStatus.PENDING]) == 2
        assert len(result[TaskStatus.IN_PROGRESS]) == 1
        assert len(result[TaskStatus.COMPLETE]) == 1
        assert len(result[TaskStatus.FAILED]) == 0


class TestGetTaskCounts:
    """Tests for get_task_counts function."""

    def test_empty_list(self):
        result = get_task_counts([])
        assert result["total"] == 0
        assert result["pending"] == 0
        assert result["in_progress"] == 0

    def test_counts_correctly(self):
        tasks = [
            Task(id="T-1", title="A", status=TaskStatus.PENDING),
            Task(id="T-2", title="B", status=TaskStatus.PENDING),
            Task(id="T-3", title="C", status=TaskStatus.IN_PROGRESS),
            Task(id="T-4", title="D", status=TaskStatus.COMPLETE),
            Task(id="T-5", title="E", status=TaskStatus.FAILED),
        ]
        result = get_task_counts(tasks)

        assert result["total"] == 5
        assert result["pending"] == 2
        assert result["in_progress"] == 1
        assert result["complete"] == 1
        assert result["failed"] == 1
        assert result["pending_approval"] == 0
        assert result["not_planned"] == 0
