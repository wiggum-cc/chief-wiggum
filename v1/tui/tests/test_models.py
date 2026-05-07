"""Tests for data models."""

from wiggum_tui.data.models import (
    Task,
    TaskStatus,
    Worker,
    WorkerStatus,
    LogLine,
    LogLevel,
    TokenUsage,
    ContextUsage,
    CostBreakdown,
    WorkerMetrics,
    Metrics,
    ToolCall,
    ConversationTurn,
    IterationResult,
    Conversation,
)


class TestTaskStatus:
    """Tests for TaskStatus enum."""

    def test_all_statuses_exist(self):
        assert TaskStatus.PENDING.value == "pending"
        assert TaskStatus.IN_PROGRESS.value == "in_progress"
        assert TaskStatus.PENDING_APPROVAL.value == "pending_approval"
        assert TaskStatus.COMPLETE.value == "complete"
        assert TaskStatus.NOT_PLANNED.value == "not_planned"
        assert TaskStatus.FAILED.value == "failed"


class TestWorkerStatus:
    """Tests for WorkerStatus enum."""

    def test_all_statuses_exist(self):
        assert WorkerStatus.RUNNING.value == "running"
        assert WorkerStatus.STOPPED.value == "stopped"
        assert WorkerStatus.COMPLETED.value == "completed"
        assert WorkerStatus.FAILED.value == "failed"


class TestLogLevel:
    """Tests for LogLevel enum."""

    def test_all_levels_exist(self):
        assert LogLevel.DEBUG.value == "DEBUG"
        assert LogLevel.INFO.value == "INFO"
        assert LogLevel.WARN.value == "WARN"
        assert LogLevel.ERROR.value == "ERROR"


class TestTask:
    """Tests for Task dataclass."""

    def test_minimal_task(self):
        task = Task(id="TASK-001", title="Test", status=TaskStatus.PENDING)
        assert task.id == "TASK-001"
        assert task.title == "Test"
        assert task.status == TaskStatus.PENDING
        assert task.description == ""
        assert task.priority == "MEDIUM"
        assert task.complexity is None
        assert task.dependencies == []
        assert task.scope == []
        assert task.out_of_scope == []
        assert task.acceptance_criteria == []
        assert task.is_running is None
        assert task.start_time is None

    def test_full_task(self):
        task = Task(
            id="TASK-001",
            title="Full Test",
            status=TaskStatus.IN_PROGRESS,
            description="A full description",
            priority="HIGH",
            complexity="MEDIUM",
            dependencies=["TASK-000"],
            scope=["Do this", "Do that"],
            out_of_scope=["Not this"],
            acceptance_criteria=["AC1", "AC2"],
            is_running=True,
            start_time=1700000000,
        )
        assert task.description == "A full description"
        assert task.priority == "HIGH"
        assert task.complexity == "MEDIUM"
        assert task.dependencies == ["TASK-000"]
        assert len(task.scope) == 2
        assert task.is_running is True


class TestWorker:
    """Tests for Worker dataclass."""

    def test_minimal_worker(self):
        worker = Worker(
            id="worker-TASK-001-1700000000",
            task_id="TASK-001",
            timestamp=1700000000,
            pid=None,
            status=WorkerStatus.STOPPED,
            prd_path="/path/prd.md",
            log_path="/path/worker.log",
            workspace_path="/path/workspace",
        )
        assert worker.id == "worker-TASK-001-1700000000"
        assert worker.task_id == "TASK-001"
        assert worker.pid is None
        assert worker.pr_url is None

    def test_worker_with_pr(self):
        worker = Worker(
            id="w1",
            task_id="T-1",
            timestamp=1,
            pid=12345,
            status=WorkerStatus.COMPLETED,
            prd_path="",
            log_path="",
            workspace_path="",
            pr_url="https://github.com/org/repo/pull/123",
        )
        assert worker.pid == 12345
        assert worker.pr_url == "https://github.com/org/repo/pull/123"


class TestLogLine:
    """Tests for LogLine dataclass."""

    def test_minimal_log_line(self):
        line = LogLine(raw="raw content")
        assert line.raw == "raw content"
        assert line.timestamp is None
        assert line.level is None
        assert line.message == ""

    def test_full_log_line(self):
        line = LogLine(
            raw="[2024-01-15 10:00:00] INFO: Message",
            timestamp="2024-01-15 10:00:00",
            level=LogLevel.INFO,
            message="Message",
        )
        assert line.timestamp == "2024-01-15 10:00:00"
        assert line.level == LogLevel.INFO
        assert line.message == "Message"


class TestTokenUsage:
    """Tests for TokenUsage dataclass."""

    def test_defaults(self):
        usage = TokenUsage()
        assert usage.input == 0
        assert usage.output == 0
        assert usage.cache_creation == 0
        assert usage.cache_read == 0
        assert usage.total == 0

    def test_with_values(self):
        usage = TokenUsage(
            input=5000, output=1000, cache_creation=500, cache_read=3000, total=9500
        )
        assert usage.input == 5000
        assert usage.total == 9500


class TestContextUsage:
    """Tests for ContextUsage dataclass."""

    def test_defaults(self):
        context = ContextUsage()
        assert context.tokens == 0
        assert context.size == 200000
        assert context.percent == 0.0

    def test_with_values(self):
        context = ContextUsage(tokens=50000, size=200000, percent=25.0)
        assert context.percent == 25.0


class TestCostBreakdown:
    """Tests for CostBreakdown dataclass."""

    def test_defaults(self):
        cost = CostBreakdown()
        assert cost.input == 0.0
        assert cost.output == 0.0
        assert cost.cache_creation == 0.0
        assert cost.cache_read == 0.0
        assert cost.total == 0.0


class TestWorkerMetrics:
    """Tests for WorkerMetrics dataclass."""

    def test_creation(self):
        metrics = WorkerMetrics(
            worker_id="worker-TEST-001-1700000000",
            status="success",
            time_spent="00:15:30",
            time_seconds=930,
            tokens=TokenUsage(input=5000, output=1000, total=6000),
            cost=0.50,
            pr_url="https://github.com/org/repo/pull/1",
        )
        assert metrics.worker_id == "worker-TEST-001-1700000000"
        assert metrics.status == "success"
        assert metrics.cost == 0.50


class TestMetrics:
    """Tests for Metrics dataclass."""

    def test_defaults(self):
        metrics = Metrics()
        assert metrics.total_workers == 0
        assert metrics.successful_workers == 0
        assert metrics.failed_workers == 0
        assert metrics.success_rate == 0.0
        assert metrics.total_time == "00:00:00"
        assert metrics.total_cost == 0.0
        assert metrics.workers == []


class TestToolCall:
    """Tests for ToolCall dataclass."""

    def test_creation(self):
        tool = ToolCall(name="Read", input={"file_path": "/test.py"})
        assert tool.name == "Read"
        assert tool.input == {"file_path": "/test.py"}
        assert tool.result is None

    def test_with_result(self):
        tool = ToolCall(
            name="Bash", input={"command": "ls"}, result={"stdout": "file1\nfile2"}
        )
        assert tool.result == {"stdout": "file1\nfile2"}


class TestConversationTurn:
    """Tests for ConversationTurn dataclass."""

    def test_defaults(self):
        turn = ConversationTurn(iteration=0)
        assert turn.iteration == 0
        assert turn.assistant_text is None
        assert turn.tool_calls == []
        assert turn.timestamp is None
        assert turn.log_name == ""

    def test_with_tool_calls(self):
        turn = ConversationTurn(
            iteration=1,
            assistant_text="I will help you.",
            tool_calls=[
                ToolCall(name="Read", input={}),
                ToolCall(name="Write", input={}),
            ],
            timestamp="2024-01-15T10:00:00Z",
            log_name="iteration-1",
        )
        assert turn.assistant_text == "I will help you."
        assert len(turn.tool_calls) == 2


class TestIterationResult:
    """Tests for IterationResult dataclass."""

    def test_defaults(self):
        result = IterationResult(iteration=0, subtype="success")
        assert result.iteration == 0
        assert result.subtype == "success"
        assert result.duration_ms == 0
        assert result.num_turns == 0
        assert result.total_cost_usd == 0.0
        assert result.is_error is False

    def test_with_values(self):
        result = IterationResult(
            iteration=2,
            subtype="max_turns_reached",
            duration_ms=30000,
            duration_api_ms=25000,
            num_turns=10,
            total_cost_usd=0.50,
            is_error=True,
            usage=TokenUsage(input=10000, output=3000, total=13000),
            log_name="iteration-2",
        )
        assert result.is_error is True
        assert result.usage.total == 13000


class TestConversation:
    """Tests for Conversation dataclass."""

    def test_defaults(self):
        conv = Conversation(worker_id="test-worker")
        assert conv.worker_id == "test-worker"
        assert conv.system_prompt == ""
        assert conv.user_prompt == ""
        assert conv.turns == []
        assert conv.results == []

    def test_with_data(self):
        conv = Conversation(
            worker_id="worker-TEST-001",
            system_prompt="You are helpful.",
            user_prompt="Fix the bug.",
            turns=[ConversationTurn(iteration=0, assistant_text="Done.")],
            results=[IterationResult(iteration=0, subtype="success")],
        )
        assert len(conv.turns) == 1
        assert len(conv.results) == 1
