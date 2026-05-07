"""Tests for worker_scanner module."""

from pathlib import Path
from unittest.mock import patch

from wiggum_tui.data.worker_scanner import (
    scan_workers,
    get_prd_status,
    get_worker_counts,
    get_running_worker_for_task,
    get_task_running_status,
    WORKER_PATTERN,
)
from wiggum_tui.data.models import Worker, WorkerStatus


class TestWorkerPattern:
    """Tests for the worker directory regex pattern."""

    def test_matches_valid_worker_names(self):
        valid_names = [
            "worker-TASK-001-1700000000",
            "worker-DEV-42-1234567890",
            "worker-TEST-1-9999999999",
            "worker-ABCDEFGHIJ-9999-1111111111",
        ]
        for name in valid_names:
            match = WORKER_PATTERN.match(name)
            assert match is not None, f"Should match: {name}"

    def test_extracts_task_id_and_timestamp(self):
        match = WORKER_PATTERN.match("worker-TASK-001-1700000000")
        assert match is not None
        task_id, timestamp = match.groups()
        assert task_id == "TASK-001"
        assert timestamp == "1700000000"

    def test_no_match_invalid_names(self):
        invalid_names = [
            "worker-TASK-001",  # Missing timestamp
            "TASK-001-1700000000",  # Missing worker- prefix
            "worker-A-1-1700000000",  # Prefix too short
            "worker-TASK-12345-1700000000",  # Number too long
        ]
        for name in invalid_names:
            assert WORKER_PATTERN.match(name) is None, f"Should not match: {name}"


class TestGetPrdStatus:
    """Tests for get_prd_status function."""

    def test_complete_prd(self, tmp_path: Path):
        prd = tmp_path / "prd.md"
        prd.write_text("# PRD\n- [x] Task 1\n- [x] Task 2\n")
        assert get_prd_status(prd) == "complete"

    def test_incomplete_prd(self, tmp_path: Path):
        prd = tmp_path / "prd.md"
        prd.write_text("# PRD\n- [x] Task 1\n- [ ] Task 2\n")
        assert get_prd_status(prd) == "incomplete"

    def test_failed_prd(self, tmp_path: Path):
        prd = tmp_path / "prd.md"
        prd.write_text("# PRD\n- [x] Task 1\n- [*] Task 2\n")
        assert get_prd_status(prd) == "failed"

    def test_failed_takes_precedence(self, tmp_path: Path):
        prd = tmp_path / "prd.md"
        prd.write_text("# PRD\n- [ ] Task 1\n- [*] Task 2\n")
        assert get_prd_status(prd) == "failed"

    def test_missing_file(self, tmp_path: Path):
        prd = tmp_path / "nonexistent.md"
        assert get_prd_status(prd) == "incomplete"

    def test_empty_prd(self, tmp_path: Path):
        prd = tmp_path / "prd.md"
        prd.write_text("")
        assert get_prd_status(prd) == "complete"


class TestScanWorkers:
    """Tests for scan_workers function."""

    def test_no_workers_directory(self, tmp_path: Path):
        ralph_dir = tmp_path / ".ralph"
        ralph_dir.mkdir()
        workers = scan_workers(ralph_dir)
        assert workers == []

    def test_empty_workers_directory(self, tmp_path: Path):
        ralph_dir = tmp_path / ".ralph"
        ralph_dir.mkdir()
        (ralph_dir / "workers").mkdir()
        workers = scan_workers(ralph_dir)
        assert workers == []

    def test_ignores_non_worker_directories(self, tmp_path: Path):
        ralph_dir = tmp_path / ".ralph"
        workers_dir = ralph_dir / "workers"
        workers_dir.mkdir(parents=True)

        # Create non-worker directories
        (workers_dir / "somefile.txt").write_text("ignored")
        (workers_dir / "random-dir").mkdir()
        (workers_dir / "worker-invalid").mkdir()  # Invalid format

        workers = scan_workers(ralph_dir)
        assert workers == []

    def test_scans_worker_directory(self, tmp_path: Path):
        ralph_dir = tmp_path / ".ralph"
        workers_dir = ralph_dir / "workers"
        worker_dir = workers_dir / "worker-TASK-001-1700000000"
        worker_dir.mkdir(parents=True)

        # Create required files (no agent.pid = not running)
        (worker_dir / "prd.md").write_text("- [x] Done")
        (worker_dir / "worker.log").write_text("log content")

        workers = scan_workers(ralph_dir)

        assert len(workers) == 1
        assert workers[0].id == "worker-TASK-001-1700000000"
        assert workers[0].task_id == "TASK-001"
        assert workers[0].status == WorkerStatus.COMPLETED

    def test_detects_running_worker(self, tmp_path: Path):
        ralph_dir = tmp_path / ".ralph"
        workers_dir = ralph_dir / "workers"
        worker_dir = workers_dir / "worker-TASK-001-1700000000"
        worker_dir.mkdir(parents=True)

        # Create PID file - presence indicates running
        (worker_dir / "agent.pid").write_text("12345")
        (worker_dir / "prd.md").write_text("- [ ] Not done")

        workers = scan_workers(ralph_dir)

        assert len(workers) == 1
        assert workers[0].status == WorkerStatus.RUNNING
        assert workers[0].pid == 12345

    def test_detects_failed_worker(self, tmp_path: Path):
        ralph_dir = tmp_path / ".ralph"
        workers_dir = ralph_dir / "workers"
        worker_dir = workers_dir / "worker-TASK-001-1700000000"
        worker_dir.mkdir(parents=True)

        # No agent.pid = not running, PRD has failed marker
        (worker_dir / "prd.md").write_text("- [*] Failed task")

        workers = scan_workers(ralph_dir)

        assert len(workers) == 1
        assert workers[0].status == WorkerStatus.FAILED

    def test_reads_pr_url(self, tmp_path: Path):
        ralph_dir = tmp_path / ".ralph"
        workers_dir = ralph_dir / "workers"
        worker_dir = workers_dir / "worker-TASK-001-1700000000"
        worker_dir.mkdir(parents=True)

        (worker_dir / "prd.md").write_text("- [x] Done")
        (worker_dir / "pr_url.txt").write_text("https://github.com/example/pr/123")

        workers = scan_workers(ralph_dir)

        assert len(workers) == 1
        assert workers[0].pr_url == "https://github.com/example/pr/123"

    def test_sorts_by_timestamp_descending(self, tmp_path: Path):
        ralph_dir = tmp_path / ".ralph"
        workers_dir = ralph_dir / "workers"

        # Create workers with different timestamps in directory name
        for name in [
            "worker-TASK-001-1700000001",
            "worker-TASK-002-1700000002",
            "worker-TASK-003-1700000003",
        ]:
            worker_dir = workers_dir / name
            worker_dir.mkdir(parents=True)
            (worker_dir / "prd.md").write_text("- [x] Done")

        workers = scan_workers(ralph_dir)

        assert len(workers) == 3
        # Should be sorted by timestamp descending (newest first)
        assert workers[0].task_id == "TASK-003"
        assert workers[1].task_id == "TASK-002"
        assert workers[2].task_id == "TASK-001"

    def test_running_worker_uses_pid_mtime_for_timestamp(self, tmp_path: Path):

        ralph_dir = tmp_path / ".ralph"
        workers_dir = ralph_dir / "workers"
        # Directory name has old timestamp
        worker_dir = workers_dir / "worker-TASK-001-1600000000"
        worker_dir.mkdir(parents=True)

        (worker_dir / "prd.md").write_text("- [ ] In progress")
        pid_file = worker_dir / "agent.pid"
        pid_file.write_text("12345")

        # Get the pid file mtime
        pid_mtime = int(pid_file.stat().st_mtime)

        workers = scan_workers(ralph_dir)

        assert len(workers) == 1
        assert workers[0].status == WorkerStatus.RUNNING
        # Running worker should use agent.pid mtime, not directory timestamp
        assert workers[0].timestamp == pid_mtime
        assert workers[0].timestamp != 1600000000

    def test_stopped_worker_uses_directory_timestamp(self, tmp_path: Path):
        ralph_dir = tmp_path / ".ralph"
        workers_dir = ralph_dir / "workers"
        worker_dir = workers_dir / "worker-TASK-001-1700000000"
        worker_dir.mkdir(parents=True)

        # No agent.pid = stopped, should use directory timestamp
        (worker_dir / "prd.md").write_text("- [ ] In progress")

        workers = scan_workers(ralph_dir)

        assert len(workers) == 1
        assert workers[0].status == WorkerStatus.STOPPED
        # Stopped worker should use directory timestamp
        assert workers[0].timestamp == 1700000000

    def test_fixture_ralph_with_workers(self, ralph_with_workers: Path):
        # This test uses the fixture which has a worker directory
        # No agent.pid means not running
        workers = scan_workers(ralph_with_workers)

        assert len(workers) >= 1
        # Find the TEST-001 worker
        test_worker = next(
            (w for w in workers if w.task_id == "TEST-001"), None
        )
        assert test_worker is not None


class TestGetWorkerCounts:
    """Tests for get_worker_counts function."""

    def test_empty_list(self):
        result = get_worker_counts([])
        assert result["total"] == 0
        assert result["running"] == 0
        assert result["completed"] == 0

    def test_counts_correctly(self):
        workers = [
            Worker(
                id="w1",
                task_id="T-1",
                timestamp=1,
                pid=None,
                status=WorkerStatus.RUNNING,
                prd_path="",
                log_path="",
                workspace_path="",
            ),
            Worker(
                id="w2",
                task_id="T-2",
                timestamp=2,
                pid=None,
                status=WorkerStatus.RUNNING,
                prd_path="",
                log_path="",
                workspace_path="",
            ),
            Worker(
                id="w3",
                task_id="T-3",
                timestamp=3,
                pid=None,
                status=WorkerStatus.COMPLETED,
                prd_path="",
                log_path="",
                workspace_path="",
            ),
            Worker(
                id="w4",
                task_id="T-4",
                timestamp=4,
                pid=None,
                status=WorkerStatus.FAILED,
                prd_path="",
                log_path="",
                workspace_path="",
            ),
        ]
        result = get_worker_counts(workers)

        assert result["total"] == 4
        assert result["running"] == 2
        assert result["completed"] == 1
        assert result["failed"] == 1
        assert result["stopped"] == 0


class TestGetRunningWorkerForTask:
    """Tests for get_running_worker_for_task function."""

    @patch("wiggum_tui.data.worker_scanner.scan_workers")
    def test_finds_running_worker(self, mock_scan):
        mock_scan.return_value = [
            Worker(
                id="w1",
                task_id="TASK-001",
                timestamp=1,
                pid=123,
                status=WorkerStatus.RUNNING,
                prd_path="",
                log_path="",
                workspace_path="",
            ),
        ]
        result = get_running_worker_for_task(Path("/fake"), "TASK-001")
        assert result is not None
        assert result.task_id == "TASK-001"

    @patch("wiggum_tui.data.worker_scanner.scan_workers")
    def test_returns_none_if_not_running(self, mock_scan):
        mock_scan.return_value = [
            Worker(
                id="w1",
                task_id="TASK-001",
                timestamp=1,
                pid=None,
                status=WorkerStatus.COMPLETED,
                prd_path="",
                log_path="",
                workspace_path="",
            ),
        ]
        result = get_running_worker_for_task(Path("/fake"), "TASK-001")
        assert result is None

    @patch("wiggum_tui.data.worker_scanner.scan_workers")
    def test_returns_none_if_not_found(self, mock_scan):
        mock_scan.return_value = []
        result = get_running_worker_for_task(Path("/fake"), "TASK-001")
        assert result is None


class TestGetTaskRunningStatus:
    """Tests for get_task_running_status function."""

    @patch("wiggum_tui.data.worker_scanner.scan_workers")
    def test_returns_status_for_multiple_tasks(self, mock_scan):
        mock_scan.return_value = [
            Worker(
                id="w1",
                task_id="TASK-001",
                timestamp=1000,
                pid=123,
                status=WorkerStatus.RUNNING,
                prd_path="",
                log_path="",
                workspace_path="",
            ),
            Worker(
                id="w2",
                task_id="TASK-002",
                timestamp=2000,
                pid=None,
                status=WorkerStatus.COMPLETED,
                prd_path="",
                log_path="",
                workspace_path="",
            ),
        ]
        result = get_task_running_status(
            Path("/fake"), ["TASK-001", "TASK-002", "TASK-003"]
        )

        assert result["TASK-001"] == (True, 1000)
        assert result["TASK-002"] == (False, None)
        assert result["TASK-003"] == (False, None)


class TestHistoryDirectory:
    """Tests for scanning history directory."""

    def test_scans_history_directory(self, tmp_path: Path):
        ralph_dir = tmp_path / ".ralph"
        history_dir = ralph_dir / "history"
        worker_dir = history_dir / "worker-TASK-001-1700000000"
        worker_dir.mkdir(parents=True)

        (worker_dir / "prd.md").write_text("- [x] Done")

        workers = scan_workers(ralph_dir)

        assert len(workers) == 1
        assert workers[0].id == "worker-TASK-001-1700000000"
        assert workers[0].task_id == "TASK-001"
        assert workers[0].is_archived is True
        # Archived workers should be marked as merged
        assert workers[0].status == WorkerStatus.MERGED

    def test_scans_both_workers_and_history(self, tmp_path: Path):
        ralph_dir = tmp_path / ".ralph"

        # Create active worker
        workers_dir = ralph_dir / "workers"
        active_worker = workers_dir / "worker-TASK-001-1700000001"
        active_worker.mkdir(parents=True)
        (active_worker / "prd.md").write_text("- [x] Done")

        # Create archived worker
        history_dir = ralph_dir / "history"
        archived_worker = history_dir / "worker-TASK-002-1700000000"
        archived_worker.mkdir(parents=True)
        (archived_worker / "prd.md").write_text("- [x] Done")

        workers = scan_workers(ralph_dir)

        assert len(workers) == 2

        # Find each worker
        active = next(w for w in workers if w.task_id == "TASK-001")
        archived = next(w for w in workers if w.task_id == "TASK-002")

        assert active.is_archived is False
        assert active.status == WorkerStatus.COMPLETED

        assert archived.is_archived is True
        assert archived.status == WorkerStatus.MERGED

    def test_include_history_false(self, tmp_path: Path):
        ralph_dir = tmp_path / ".ralph"

        # Create active worker
        workers_dir = ralph_dir / "workers"
        active_worker = workers_dir / "worker-TASK-001-1700000001"
        active_worker.mkdir(parents=True)
        (active_worker / "prd.md").write_text("- [x] Done")

        # Create archived worker
        history_dir = ralph_dir / "history"
        archived_worker = history_dir / "worker-TASK-002-1700000000"
        archived_worker.mkdir(parents=True)
        (archived_worker / "prd.md").write_text("- [x] Done")

        # Scan without history
        workers = scan_workers(ralph_dir, include_history=False)

        assert len(workers) == 1
        assert workers[0].task_id == "TASK-001"
        assert workers[0].is_archived is False

    def test_archived_failed_worker_keeps_failed_status(self, tmp_path: Path):
        ralph_dir = tmp_path / ".ralph"
        history_dir = ralph_dir / "history"
        worker_dir = history_dir / "worker-TASK-001-1700000000"
        worker_dir.mkdir(parents=True)

        # Failed marker in PRD
        (worker_dir / "prd.md").write_text("- [*] Failed task")

        workers = scan_workers(ralph_dir)

        assert len(workers) == 1
        assert workers[0].is_archived is True
        # Failed workers should keep failed status even when archived
        assert workers[0].status == WorkerStatus.FAILED

    def test_deduplicates_same_worker_in_both_dirs(self, tmp_path: Path):
        """When same worker ID exists in both workers/ and history/, prefer non-archived."""
        ralph_dir = tmp_path / ".ralph"

        # Create worker in workers/ (non-archived)
        workers_dir = ralph_dir / "workers"
        active_worker = workers_dir / "worker-TASK-001-1700000000"
        active_worker.mkdir(parents=True)
        (active_worker / "prd.md").write_text("- [ ] In progress")

        # Create same worker ID in history/ (archived)
        history_dir = ralph_dir / "history"
        archived_worker = history_dir / "worker-TASK-001-1700000000"
        archived_worker.mkdir(parents=True)
        (archived_worker / "prd.md").write_text("- [x] Done")

        workers = scan_workers(ralph_dir)

        # Should be deduplicated to one entry
        assert len(workers) == 1
        # Should prefer non-archived version
        assert workers[0].is_archived is False
        assert workers[0].status == WorkerStatus.STOPPED  # Non-archived, incomplete PRD
