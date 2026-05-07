"""Tests for log_reader module."""

from pathlib import Path

from wiggum_tui.data.log_reader import (
    parse_log_line,
    read_log,
    tail_log,
    filter_by_level,
    search_logs,
    LogTailer,
    LOG_PATTERN,
)
from wiggum_tui.data.models import LogLine, LogLevel


class TestLogPattern:
    """Tests for the log line regex pattern."""

    def test_matches_valid_log_lines(self):
        valid_lines = [
            "[2024-01-15 10:00:00] INFO: Message here",
            "[2024-01-15 10:00:00] DEBUG: Debug message",
            "[2024-01-15 10:00:00] WARN: Warning message",
            "[2024-01-15 10:00:00] ERROR: Error message",
        ]
        for line in valid_lines:
            match = LOG_PATTERN.match(line)
            assert match is not None, f"Should match: {line}"

    def test_extracts_components(self):
        line = "[2024-01-15 10:30:45] INFO: Task started successfully"
        match = LOG_PATTERN.match(line)
        assert match is not None
        timestamp, level, message = match.groups()
        assert timestamp == "2024-01-15 10:30:45"
        assert level == "INFO"
        assert message == "Task started successfully"

    def test_no_match_invalid_lines(self):
        invalid_lines = [
            "2024-01-15 10:00:00 INFO: Missing brackets",
            "[2024-01-15 10:00:00] INVALID: Unknown level",
            "Just plain text",
            "",
        ]
        for line in invalid_lines:
            assert LOG_PATTERN.match(line) is None, f"Should not match: {line}"


class TestParseLogLine:
    """Tests for parse_log_line function."""

    def test_parses_info_line(self):
        result = parse_log_line("[2024-01-15 10:00:00] INFO: Starting process")
        assert result.timestamp == "2024-01-15 10:00:00"
        assert result.level == LogLevel.INFO
        assert result.message == "Starting process"
        assert result.raw == "[2024-01-15 10:00:00] INFO: Starting process"

    def test_parses_debug_line(self):
        result = parse_log_line("[2024-01-15 10:00:00] DEBUG: Debug info")
        assert result.level == LogLevel.DEBUG

    def test_parses_warn_line(self):
        result = parse_log_line("[2024-01-15 10:00:00] WARN: Warning!")
        assert result.level == LogLevel.WARN

    def test_parses_error_line(self):
        result = parse_log_line("[2024-01-15 10:00:00] ERROR: Something failed")
        assert result.level == LogLevel.ERROR

    def test_handles_non_matching_line(self):
        result = parse_log_line("Just some text without format")
        assert result.timestamp is None
        assert result.level is None
        assert result.message == "Just some text without format"
        assert result.raw == "Just some text without format"

    def test_strips_newlines(self):
        result = parse_log_line("[2024-01-15 10:00:00] INFO: Message\n")
        assert result.message == "Message"
        assert "\n" not in result.raw


class TestReadLog:
    """Tests for read_log function."""

    def test_file_not_found(self, tmp_path: Path):
        result = read_log(tmp_path / "nonexistent.log")
        assert result == []

    def test_reads_all_lines(self, tmp_path: Path):
        log_file = tmp_path / "test.log"
        log_file.write_text(
            "[2024-01-15 10:00:00] INFO: Line 1\n"
            "[2024-01-15 10:00:01] INFO: Line 2\n"
            "[2024-01-15 10:00:02] INFO: Line 3\n"
        )
        result = read_log(log_file)
        assert len(result) == 3
        assert result[0].message == "Line 1"
        assert result[2].message == "Line 3"

    def test_respects_max_lines(self, tmp_path: Path):
        log_file = tmp_path / "test.log"
        lines = "\n".join(
            f"[2024-01-15 10:00:{i:02d}] INFO: Line {i}" for i in range(100)
        )
        log_file.write_text(lines)

        result = read_log(log_file, max_lines=10)
        assert len(result) == 10
        # Should return last 10 lines
        assert result[0].message == "Line 90"
        assert result[9].message == "Line 99"

    def test_skips_empty_lines(self, tmp_path: Path):
        log_file = tmp_path / "test.log"
        log_file.write_text(
            "[2024-01-15 10:00:00] INFO: Line 1\n"
            "\n"
            "[2024-01-15 10:00:02] INFO: Line 2\n"
            "   \n"
        )
        result = read_log(log_file)
        assert len(result) == 2

    def test_fixture_combined_log(self, ralph_with_workers: Path):
        log_file = ralph_with_workers / "logs" / "combined.log"
        result = read_log(log_file)
        assert len(result) > 0
        # Check we got some expected content
        levels = {log.level for log in result if log.level}
        assert LogLevel.INFO in levels


class TestTailLog:
    """Tests for tail_log function."""

    def test_file_not_found(self, tmp_path: Path):
        result = tail_log(tmp_path / "nonexistent.log")
        assert result == []

    def test_reads_last_n_lines(self, tmp_path: Path):
        log_file = tmp_path / "test.log"
        lines = "\n".join(
            f"[2024-01-15 10:00:{i:02d}] INFO: Line {i}" for i in range(50)
        )
        log_file.write_text(lines)

        result = tail_log(log_file, max_lines=5)
        assert len(result) == 5
        assert result[0].message == "Line 45"
        assert result[4].message == "Line 49"

    def test_handles_small_file(self, tmp_path: Path):
        log_file = tmp_path / "test.log"
        log_file.write_text("[2024-01-15 10:00:00] INFO: Only line\n")

        result = tail_log(log_file, max_lines=100)
        assert len(result) == 1


class TestFilterByLevel:
    """Tests for filter_by_level function."""

    def test_no_filter(self):
        logs = [
            LogLine(raw="", level=LogLevel.DEBUG, message="debug"),
            LogLine(raw="", level=LogLevel.INFO, message="info"),
            LogLine(raw="", level=LogLevel.WARN, message="warn"),
            LogLine(raw="", level=LogLevel.ERROR, message="error"),
        ]
        result = filter_by_level(logs, min_level=None)
        assert len(result) == 4

    def test_filter_info_and_above(self):
        logs = [
            LogLine(raw="", level=LogLevel.DEBUG, message="debug"),
            LogLine(raw="", level=LogLevel.INFO, message="info"),
            LogLine(raw="", level=LogLevel.WARN, message="warn"),
            LogLine(raw="", level=LogLevel.ERROR, message="error"),
        ]
        result = filter_by_level(logs, min_level=LogLevel.INFO)
        assert len(result) == 3
        assert all(log.level != LogLevel.DEBUG for log in result)

    def test_filter_warn_and_above(self):
        logs = [
            LogLine(raw="", level=LogLevel.DEBUG, message="debug"),
            LogLine(raw="", level=LogLevel.INFO, message="info"),
            LogLine(raw="", level=LogLevel.WARN, message="warn"),
            LogLine(raw="", level=LogLevel.ERROR, message="error"),
        ]
        result = filter_by_level(logs, min_level=LogLevel.WARN)
        assert len(result) == 2
        levels = {log.level for log in result}
        assert levels == {LogLevel.WARN, LogLevel.ERROR}

    def test_filter_error_only(self):
        logs = [
            LogLine(raw="", level=LogLevel.DEBUG, message="debug"),
            LogLine(raw="", level=LogLevel.INFO, message="info"),
            LogLine(raw="", level=LogLevel.WARN, message="warn"),
            LogLine(raw="", level=LogLevel.ERROR, message="error"),
        ]
        result = filter_by_level(logs, min_level=LogLevel.ERROR)
        assert len(result) == 1
        assert result[0].level == LogLevel.ERROR

    def test_includes_lines_without_level(self):
        logs = [
            LogLine(raw="", level=None, message="no level"),
            LogLine(raw="", level=LogLevel.DEBUG, message="debug"),
            LogLine(raw="", level=LogLevel.ERROR, message="error"),
        ]
        result = filter_by_level(logs, min_level=LogLevel.ERROR)
        # Lines without level should be included
        assert len(result) == 2


class TestSearchLogs:
    """Tests for search_logs function."""

    def test_case_insensitive_search(self):
        logs = [
            LogLine(raw="[time] INFO: Error occurred", message="Error occurred"),
            LogLine(raw="[time] INFO: error again", message="error again"),
            LogLine(raw="[time] INFO: No match here", message="No match here"),
        ]
        result = search_logs(logs, "error")
        assert len(result) == 2

    def test_searches_raw_content(self):
        logs = [
            LogLine(
                raw="[2024-01-15] INFO: Message",
                timestamp="2024-01-15",
                message="Message",
            ),
        ]
        result = search_logs(logs, "2024-01-15")
        assert len(result) == 1

    def test_no_matches(self):
        logs = [
            LogLine(raw="Line 1", message="Line 1"),
            LogLine(raw="Line 2", message="Line 2"),
        ]
        result = search_logs(logs, "xyz")
        assert len(result) == 0


class TestLogTailer:
    """Tests for LogTailer class."""

    def test_initial_read(self, tmp_path: Path):
        log_file = tmp_path / "test.log"
        log_file.write_text(
            "[2024-01-15 10:00:00] INFO: Line 1\n"
            "[2024-01-15 10:00:01] INFO: Line 2\n"
        )

        tailer = LogTailer(log_file, max_buffer=100)
        new_lines = tailer.get_new_lines()

        assert len(new_lines) == 2
        assert tailer._initialized

    def test_incremental_read(self, tmp_path: Path):
        log_file = tmp_path / "test.log"
        log_file.write_text("[2024-01-15 10:00:00] INFO: Line 1\n")

        tailer = LogTailer(log_file, max_buffer=100)
        initial = tailer.get_new_lines()
        assert len(initial) == 1

        # Append more content
        with open(log_file, "a") as f:
            f.write("[2024-01-15 10:00:01] INFO: Line 2\n")
            f.write("[2024-01-15 10:00:02] INFO: Line 3\n")

        new_lines = tailer.get_new_lines()
        assert len(new_lines) == 2
        assert new_lines[0].message == "Line 2"
        assert new_lines[1].message == "Line 3"

    def test_handles_truncation(self, tmp_path: Path):
        log_file = tmp_path / "test.log"
        log_file.write_text(
            "[2024-01-15 10:00:00] INFO: Original content that is long\n"
        )

        tailer = LogTailer(log_file, max_buffer=100)
        tailer.get_new_lines()

        # Truncate the file
        log_file.write_text("[2024-01-15 10:00:00] INFO: New\n")

        new_lines = tailer.get_new_lines()
        assert len(new_lines) == 1
        assert new_lines[0].message == "New"

    def test_get_all_lines(self, tmp_path: Path):
        log_file = tmp_path / "test.log"
        log_file.write_text(
            "[2024-01-15 10:00:00] INFO: Line 1\n"
            "[2024-01-15 10:00:01] INFO: Line 2\n"
        )

        tailer = LogTailer(log_file, max_buffer=100)
        tailer.get_new_lines()

        all_lines = tailer.get_all_lines()
        assert len(all_lines) == 2

    def test_respects_max_buffer(self, tmp_path: Path):
        log_file = tmp_path / "test.log"
        lines = "\n".join(
            f"[2024-01-15 10:00:{i:02d}] INFO: Line {i}" for i in range(100)
        )
        log_file.write_text(lines)

        tailer = LogTailer(log_file, max_buffer=10)
        tailer.get_new_lines()

        all_lines = tailer.get_all_lines()
        assert len(all_lines) == 10

    def test_file_not_found(self, tmp_path: Path):
        log_file = tmp_path / "nonexistent.log"
        tailer = LogTailer(log_file)
        result = tailer.get_new_lines()
        assert result == []
