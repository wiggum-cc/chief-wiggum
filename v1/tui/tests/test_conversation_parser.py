"""Tests for conversation_parser module."""

import json
import pytest
from pathlib import Path

from wiggum_tui.data.conversation_parser import (
    parse_iteration_logs,
    parse_multiple_worker_logs,
    get_conversation_summary,
    truncate_text,
    format_tool_result,
    _parse_result,
    _group_into_turns,
)
from wiggum_tui.data.models import (
    Conversation,
    ConversationTurn,
    ToolCall,
    IterationResult,
    TokenUsage,
)


class TestParseIterationLogs:
    """Tests for parse_iteration_logs function."""

    def test_no_logs_directory(self, tmp_path: Path):
        worker_dir = tmp_path / "worker-TEST-001-1700000000"
        worker_dir.mkdir()
        # No logs/ subdirectory

        result = parse_iteration_logs(worker_dir)

        assert result.worker_id == "worker-TEST-001-1700000000"
        assert result.turns == []
        assert result.results == []

    def test_empty_logs_directory(self, tmp_path: Path):
        worker_dir = tmp_path / "worker-TEST-001-1700000000"
        (worker_dir / "logs").mkdir(parents=True)

        result = parse_iteration_logs(worker_dir)

        assert result.turns == []

    def test_parses_system_and_user_prompt(self, tmp_path: Path):
        worker_dir = tmp_path / "worker-TEST-001-1700000000"
        logs_dir = worker_dir / "logs"
        logs_dir.mkdir(parents=True)

        log_content = json.dumps(
            {
                "type": "iteration_start",
                "iteration": 0,
                "system_prompt": "You are helpful.",
                "user_prompt": "Fix the bug.",
            }
        )
        (logs_dir / "iteration-0.log").write_text(log_content + "\n")

        result = parse_iteration_logs(worker_dir)

        assert result.system_prompt == "You are helpful."
        assert result.user_prompt == "Fix the bug."

    def test_parses_assistant_text(self, tmp_path: Path):
        worker_dir = tmp_path / "worker-TEST-001-1700000000"
        logs_dir = worker_dir / "logs"
        logs_dir.mkdir(parents=True)

        entries = [
            {
                "type": "assistant",
                "timestamp": "2024-01-15T10:00:00Z",
                "message": {"content": [{"type": "text", "text": "I will help you."}]},
            }
        ]
        log_content = "\n".join(json.dumps(e) for e in entries)
        (logs_dir / "iteration-0.log").write_text(log_content + "\n")

        result = parse_iteration_logs(worker_dir)

        assert len(result.turns) == 1
        assert result.turns[0].assistant_text == "I will help you."

    def test_parses_tool_calls(self, tmp_path: Path):
        worker_dir = tmp_path / "worker-TEST-001-1700000000"
        logs_dir = worker_dir / "logs"
        logs_dir.mkdir(parents=True)

        entries = [
            {
                "type": "assistant",
                "timestamp": "2024-01-15T10:00:00Z",
                "message": {
                    "content": [
                        {
                            "type": "tool_use",
                            "id": "tool_001",
                            "name": "Read",
                            "input": {"file_path": "/path/to/file.py"},
                        }
                    ]
                },
            },
            {
                "type": "user",
                "timestamp": "2024-01-15T10:00:01Z",
                "tool_use_result": {"content": "file content here"},
                "message": {
                    "content": [
                        {
                            "type": "tool_result",
                            "tool_use_id": "tool_001",
                            "content": "file content here",
                        }
                    ]
                },
            },
        ]
        log_content = "\n".join(json.dumps(e) for e in entries)
        (logs_dir / "iteration-0.log").write_text(log_content + "\n")

        result = parse_iteration_logs(worker_dir)

        assert len(result.turns) == 1
        assert len(result.turns[0].tool_calls) == 1
        assert result.turns[0].tool_calls[0].name == "Read"
        assert result.turns[0].tool_calls[0].input == {"file_path": "/path/to/file.py"}
        assert result.turns[0].tool_calls[0].result == {"content": "file content here"}

    def test_parses_result_entries(self, tmp_path: Path):
        worker_dir = tmp_path / "worker-TEST-001-1700000000"
        logs_dir = worker_dir / "logs"
        logs_dir.mkdir(parents=True)

        entries = [
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
            }
        ]
        log_content = "\n".join(json.dumps(e) for e in entries)
        (logs_dir / "iteration-0.log").write_text(log_content + "\n")

        result = parse_iteration_logs(worker_dir)

        assert len(result.results) == 1
        assert result.results[0].subtype == "success"
        assert result.results[0].duration_ms == 15000
        assert result.results[0].total_cost_usd == 0.25
        assert result.results[0].usage.input == 5000
        assert result.results[0].usage.output == 1500

    def test_handles_invalid_json(self, tmp_path: Path):
        worker_dir = tmp_path / "worker-TEST-001-1700000000"
        logs_dir = worker_dir / "logs"
        logs_dir.mkdir(parents=True)

        # Mix valid and invalid JSON
        content = (
            '{"type": "assistant", "message": {"content": [{"type": "text", "text": "Valid"}]}}\n'
            "not valid json\n"
            '{"type": "result", "iteration": 0, "subtype": "success"}\n'
        )
        (logs_dir / "iteration-0.log").write_text(content)

        result = parse_iteration_logs(worker_dir)

        # Should parse what it can
        assert len(result.turns) == 1
        assert len(result.results) == 1

    def test_fixture_worker_logs(self, ralph_with_workers: Path):
        worker_dir = ralph_with_workers / "workers" / "worker-TEST-001-1700000000"
        result = parse_iteration_logs(worker_dir)

        assert result.worker_id == "worker-TEST-001-1700000000"
        assert result.system_prompt == "You are a helpful assistant."
        assert len(result.turns) >= 1
        assert len(result.results) >= 1

    def test_skips_subagent_messages(self, tmp_path: Path):
        worker_dir = tmp_path / "worker-TEST-001-1700000000"
        logs_dir = worker_dir / "logs"
        logs_dir.mkdir(parents=True)

        entries = [
            {
                "type": "assistant",
                "message": {"content": [{"type": "text", "text": "Main agent"}]},
            },
            {
                "type": "assistant",
                "parent_tool_use_id": "task_001",  # Subagent message
                "message": {"content": [{"type": "text", "text": "Subagent message"}]},
            },
        ]
        log_content = "\n".join(json.dumps(e) for e in entries)
        (logs_dir / "iteration-0.log").write_text(log_content + "\n")

        result = parse_iteration_logs(worker_dir)

        # Should only have the main agent turn
        assert len(result.turns) == 1
        assert result.turns[0].assistant_text == "Main agent"


class TestParseResult:
    """Tests for _parse_result function."""

    def test_parses_all_fields(self):
        entry = {
            "iteration": 2,
            "subtype": "max_turns_reached",
            "duration_ms": 30000,
            "duration_api_ms": 25000,
            "num_turns": 10,
            "total_cost_usd": 0.50,
            "is_error": True,
            "usage": {
                "input_tokens": 10000,
                "output_tokens": 3000,
                "cache_creation_input_tokens": 1000,
                "cache_read_input_tokens": 5000,
            },
        }
        result = _parse_result(entry)

        assert result.iteration == 2
        assert result.subtype == "max_turns_reached"
        assert result.duration_ms == 30000
        assert result.duration_api_ms == 25000
        assert result.num_turns == 10
        assert result.total_cost_usd == 0.50
        assert result.is_error is True
        assert result.usage.input == 10000
        assert result.usage.output == 3000
        assert result.usage.cache_creation == 1000
        assert result.usage.cache_read == 5000
        assert result.usage.total == 13000

    def test_handles_missing_fields(self):
        entry = {"type": "result"}
        result = _parse_result(entry)

        assert result.iteration == 0
        assert result.subtype == ""
        assert result.duration_ms == 0
        assert result.total_cost_usd == 0.0
        assert result.is_error is False


class TestGroupIntoTurns:
    """Tests for _group_into_turns function."""

    def test_empty_entries(self):
        result = _group_into_turns([])
        assert result == []

    def test_single_text_turn(self):
        entries = [
            {
                "type": "assistant",
                "_iteration_idx": 0,
                "_log_name": "iteration-0",
                "timestamp": "2024-01-15T10:00:00Z",
                "message": {"content": [{"type": "text", "text": "Hello!"}]},
            }
        ]
        result = _group_into_turns(entries)

        assert len(result) == 1
        assert result[0].assistant_text == "Hello!"
        assert result[0].iteration == 0
        assert result[0].log_name == "iteration-0"

    def test_text_with_tool_calls(self):
        entries = [
            {
                "type": "assistant",
                "_iteration_idx": 0,
                "_log_name": "iteration-0",
                "timestamp": "2024-01-15T10:00:00Z",
                "message": {
                    "content": [
                        {"type": "text", "text": "Let me read the file."},
                        {
                            "type": "tool_use",
                            "id": "tool_001",
                            "name": "Read",
                            "input": {"file_path": "/test.py"},
                        },
                    ]
                },
            },
            {
                "type": "user",
                "_iteration_idx": 0,
                "_log_name": "iteration-0",
                "tool_use_result": "file content",
                "message": {
                    "content": [
                        {"type": "tool_result", "tool_use_id": "tool_001", "content": "file content"}
                    ]
                },
            },
        ]
        result = _group_into_turns(entries)

        assert len(result) == 1
        assert result[0].assistant_text == "Let me read the file."
        assert len(result[0].tool_calls) == 1
        assert result[0].tool_calls[0].name == "Read"
        assert result[0].tool_calls[0].result == "file content"


class TestGetConversationSummary:
    """Tests for get_conversation_summary function."""

    def test_empty_conversation(self):
        conv = Conversation(worker_id="test")
        result = get_conversation_summary(conv)

        assert result["turns"] == 0
        assert result["tool_calls"] == 0
        assert result["cost_usd"] == 0
        assert result["tokens"] == 0

    def test_summarizes_conversation(self):
        conv = Conversation(
            worker_id="test",
            turns=[
                ConversationTurn(
                    iteration=0,
                    assistant_text="Hello",
                    tool_calls=[
                        ToolCall(name="Read", input={}),
                        ToolCall(name="Write", input={}),
                    ],
                ),
                ConversationTurn(
                    iteration=1,
                    assistant_text="Done",
                    tool_calls=[ToolCall(name="Bash", input={})],
                ),
            ],
            results=[
                IterationResult(
                    iteration=0,
                    subtype="success",
                    duration_ms=10000,
                    total_cost_usd=0.10,
                    usage=TokenUsage(input=1000, output=500),
                ),
                IterationResult(
                    iteration=1,
                    subtype="success",
                    duration_ms=5000,
                    total_cost_usd=0.05,
                    usage=TokenUsage(input=500, output=250),
                ),
            ],
        )
        result = get_conversation_summary(conv)

        assert result["turns"] == 2
        assert result["tool_calls"] == 3
        assert result["cost_usd"] == pytest.approx(0.15)
        assert result["duration_ms"] == 15000
        assert result["tokens"] == 2250
        assert result["iterations"] == 2


class TestTruncateText:
    """Tests for truncate_text function."""

    def test_short_text_unchanged(self):
        result = truncate_text("Hello", max_length=100)
        assert result == "Hello"

    def test_exact_length_unchanged(self):
        result = truncate_text("12345", max_length=5)
        assert result == "12345"

    def test_truncates_long_text(self):
        result = truncate_text("Hello World!", max_length=10)
        assert result == "Hello W..."
        assert len(result) == 10

    def test_default_max_length(self):
        long_text = "x" * 200
        result = truncate_text(long_text)
        assert len(result) == 100
        assert result.endswith("...")


class TestFormatToolResult:
    """Tests for format_tool_result function."""

    def test_none_result(self):
        result = format_tool_result(None)
        assert result == "(no result)"

    def test_text_type_with_file(self):
        result = format_tool_result(
            {"type": "text", "file": {"filePath": "/path/to/file.py"}}
        )
        assert result == "Read: /path/to/file.py"

    def test_tool_result_type(self):
        result = format_tool_result(
            {"type": "tool_result", "content": "Some output content"}
        )
        assert "Some output content" in result

    def test_stdout_result(self):
        result = format_tool_result({"stdout": "Command output"})
        assert "Command output" in result

    def test_error_result(self):
        result = format_tool_result({"error": "Something went wrong"})
        assert "Error:" in result
        assert "Something went wrong" in result

    def test_success_result(self):
        assert format_tool_result({"success": True}) == "Success"
        assert format_tool_result({"success": False}) == "Failed"

    def test_generic_dict(self):
        result = format_tool_result({"a": 1, "b": 2, "c": 3})
        assert "{...}" in result
        assert "a" in result or "b" in result or "c" in result

    def test_string_result(self):
        result = format_tool_result("Simple string result")
        assert result == "Simple string result"

    def test_truncates_long_content(self):
        long_content = "x" * 500
        result = format_tool_result({"stdout": long_content}, max_length=50)
        assert len(result) == 50
        assert result.endswith("...")


class TestParseMultipleWorkerLogs:
    """Tests for parse_multiple_worker_logs function."""

    def test_empty_list(self):
        result = parse_multiple_worker_logs([], "TASK-001")
        assert result.worker_id == "TASK-001"
        assert result.turns == []
        assert result.results == []

    def test_single_worker(self, tmp_path: Path):
        worker_dir = tmp_path / "worker-TASK-001-1700000000"
        logs_dir = worker_dir / "logs"
        logs_dir.mkdir(parents=True)

        log_content = json.dumps({
            "type": "iteration_start",
            "system_prompt": "System",
            "user_prompt": "User"
        }) + "\n" + json.dumps({
            "type": "assistant",
            "message": {"content": [{"type": "text", "text": "Hello"}]}
        })
        (logs_dir / "iteration-0.log").write_text(log_content)

        result = parse_multiple_worker_logs([(worker_dir, 1700000000)], "TASK-001")

        assert result.worker_id == "TASK-001"
        assert result.system_prompt == "System"
        assert result.user_prompt == "User"
        assert len(result.turns) == 1

    def test_combines_multiple_workers(self, tmp_path: Path):
        # Create first worker (older)
        worker1 = tmp_path / "worker-TASK-001-1700000000"
        logs1 = worker1 / "logs"
        logs1.mkdir(parents=True)
        (logs1 / "iteration-0.log").write_text(json.dumps({
            "type": "assistant",
            "message": {"content": [{"type": "text", "text": "First worker"}]}
        }))

        # Create second worker (newer)
        worker2 = tmp_path / "worker-TASK-001-1700000001"
        logs2 = worker2 / "logs"
        logs2.mkdir(parents=True)
        (logs2 / "iteration-0.log").write_text(json.dumps({
            "type": "assistant",
            "message": {"content": [{"type": "text", "text": "Second worker"}]}
        }))

        result = parse_multiple_worker_logs([
            (worker1, 1700000000),
            (worker2, 1700000001),
        ], "TASK-001")

        assert result.worker_id == "TASK-001"
        assert len(result.turns) == 2
        # Turns should be from both workers, ordered by worker timestamp
        assert "First worker" in result.turns[0].assistant_text
        assert "Second worker" in result.turns[1].assistant_text

    def test_prefixes_log_names_with_worker(self, tmp_path: Path):
        worker_dir = tmp_path / "worker-TASK-001-1700000000"
        logs_dir = worker_dir / "logs"
        logs_dir.mkdir(parents=True)
        (logs_dir / "iteration-0.log").write_text(json.dumps({
            "type": "assistant",
            "message": {"content": [{"type": "text", "text": "Hello"}]}
        }))

        result = parse_multiple_worker_logs([(worker_dir, 1700000000)], "TASK-001")

        assert len(result.turns) == 1
        # Log name should be prefixed with worker directory name
        assert "worker-TASK-001-1700000000" in result.turns[0].log_name

    def test_uses_first_non_empty_prompts(self, tmp_path: Path):
        # First worker has no prompts
        worker1 = tmp_path / "worker-TASK-001-1700000000"
        logs1 = worker1 / "logs"
        logs1.mkdir(parents=True)
        (logs1 / "iteration-0.log").write_text(json.dumps({
            "type": "assistant",
            "message": {"content": [{"type": "text", "text": "First"}]}
        }))

        # Second worker has prompts
        worker2 = tmp_path / "worker-TASK-001-1700000001"
        logs2 = worker2 / "logs"
        logs2.mkdir(parents=True)
        (logs2 / "iteration-0.log").write_text(
            json.dumps({
                "type": "iteration_start",
                "system_prompt": "System from second",
                "user_prompt": "User from second"
            }) + "\n" + json.dumps({
                "type": "assistant",
                "message": {"content": [{"type": "text", "text": "Second"}]}
            })
        )

        result = parse_multiple_worker_logs([
            (worker1, 1700000000),
            (worker2, 1700000001),
        ], "TASK-001")

        # Should use prompts from second worker since first has none
        assert result.system_prompt == "System from second"
        assert result.user_prompt == "User from second"
