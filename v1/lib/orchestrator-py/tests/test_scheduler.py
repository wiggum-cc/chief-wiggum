"""Tests for service_scheduler.py — phase dispatch and interval scheduling."""

import time
from unittest.mock import MagicMock, patch

import pytest

from wiggum_orchestrator.circuit_breaker import CircuitBreaker
from wiggum_orchestrator.config import ServiceConfig, ServiceRegistry
from wiggum_orchestrator.service_executor import ServiceExecutor
from wiggum_orchestrator.service_scheduler import ServiceScheduler
from wiggum_orchestrator.service_state import ServiceState


@pytest.fixture()
def state(tmp_path):
    return ServiceState(str(tmp_path))


@pytest.fixture()
def cb(state):
    return CircuitBreaker(state)


@pytest.fixture()
def mock_executor():
    executor = MagicMock(spec=ServiceExecutor)
    executor.run_phase.return_value = (True, 0)
    executor.run_function.return_value = 0
    executor.run_command.return_value = 0
    return executor


def _make_scheduler(services, state, mock_executor, cb):
    registry = ServiceRegistry(services)
    return ServiceScheduler(registry, state, mock_executor, cb)


def test_startup_phase_calls_bridge(state, mock_executor, cb):
    """Startup phase should collect functions and call bridge once."""
    services = [
        ServiceConfig(
            id="validate",
            phase="startup",
            order=10,
            required=True,
            execution={"type": "function", "function": "svc_orch_validate_kanban"},
        ),
        ServiceConfig(
            id="init",
            phase="startup",
            order=20,
            execution={"type": "function", "function": "svc_orch_init_scheduler"},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    result = scheduler.run_phase("startup")

    assert result is True
    mock_executor.run_phase.assert_called_once_with(
        "startup",
        ["svc_orch_validate_kanban", "svc_orch_init_scheduler"],
    )


def test_startup_failure_returns_false(state, mock_executor, cb):
    """Startup failure with required service should return False."""
    mock_executor.run_phase.return_value = (False, 1)
    services = [
        ServiceConfig(
            id="critical",
            phase="startup",
            order=10,
            required=True,
            execution={"type": "function", "function": "svc_critical"},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    result = scheduler.run_phase("startup")
    assert result is False


def test_shutdown_reverse_order(state, mock_executor, cb):
    """Shutdown phase should reverse service order."""
    services = [
        ServiceConfig(
            id="first",
            phase="shutdown",
            order=10,
            execution={"type": "function", "function": "svc_first"},
        ),
        ServiceConfig(
            id="second",
            phase="shutdown",
            order=20,
            execution={"type": "function", "function": "svc_second"},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    scheduler.run_phase("shutdown")

    mock_executor.run_phase.assert_called_once_with(
        "shutdown",
        ["svc_second", "svc_first"],  # reversed
    )


def test_periodic_interval_due(state, mock_executor, cb):
    """Periodic service should run when interval has elapsed."""
    services = [
        ServiceConfig(
            id="sync",
            phase="periodic",
            order=10,
            schedule={"type": "interval", "interval": 60, "run_on_startup": False},
            execution={"type": "function", "function": "svc_sync"},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    # Set startup complete to skip startup logic
    scheduler._startup_complete = True

    # Set last_run to long ago so it's due
    state.get("sync").last_run = time.time() - 120

    scheduler.run_phase("periodic")

    mock_executor.run_function.assert_called_once()


def test_periodic_interval_not_due(state, mock_executor, cb):
    """Periodic service should not run before interval elapsed."""
    services = [
        ServiceConfig(
            id="sync",
            phase="periodic",
            order=10,
            schedule={"type": "interval", "interval": 60, "run_on_startup": False},
            execution={"type": "function", "function": "svc_sync"},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    scheduler._startup_complete = True

    # Just ran recently
    state.get("sync").last_run = time.time()

    scheduler.run_phase("periodic")
    mock_executor.run_function.assert_not_called()


def test_periodic_continuous_runs_after_restart_delay(state, mock_executor, cb):
    """Continuous services should restart after their restart delay."""
    mock_executor.run_pipeline.return_value = 0
    services = [
        ServiceConfig(
            id="autofix",
            phase="periodic",
            order=10,
            schedule={"type": "continuous", "restart_delay": 60},
            execution={"type": "pipeline", "pipeline": "autofix"},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    scheduler._startup_complete = True

    state.get("autofix").last_run = time.time() - 120

    scheduler.run_phase("periodic")

    mock_executor.run_pipeline.assert_called_once()


def test_periodic_continuous_waits_for_restart_delay(state, mock_executor, cb):
    """Continuous services should not restart before their restart delay."""
    mock_executor.run_pipeline.return_value = 0
    services = [
        ServiceConfig(
            id="autofix",
            phase="periodic",
            order=10,
            schedule={"type": "continuous", "restart_delay": 60},
            execution={"type": "pipeline", "pipeline": "autofix"},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    scheduler._startup_complete = True

    state.get("autofix").last_run = time.time()

    scheduler.run_phase("periodic")

    mock_executor.run_pipeline.assert_not_called()


def test_periodic_circuit_breaker_blocks(state, mock_executor, cb):
    """Circuit breaker open should block periodic service."""
    services = [
        ServiceConfig(
            id="sync",
            phase="periodic",
            order=10,
            schedule={"type": "interval", "interval": 60, "run_on_startup": False},
            execution={"type": "function", "function": "svc_sync"},
            circuit_breaker={"enabled": True, "threshold": 3, "cooldown": 300},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    scheduler._startup_complete = True

    # Open circuit breaker
    entry = state.get("sync")
    entry.last_run = time.time() - 120  # interval elapsed
    entry.circuit_state = "open"
    entry.circuit_opened_at = time.time()  # just opened

    scheduler.run_phase("periodic")
    mock_executor.run_function.assert_not_called()


def test_periodic_concurrency_skip(state, mock_executor, cb):
    """Running service with max_instances=1 should be skipped."""
    services = [
        ServiceConfig(
            id="sync",
            phase="periodic",
            order=10,
            schedule={"type": "interval", "interval": 60, "run_on_startup": False},
            execution={"type": "function", "function": "svc_sync"},
            concurrency={"max_instances": 1, "if_running": "skip"},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    scheduler._startup_complete = True

    entry = state.get("sync")
    entry.last_run = time.time() - 120
    entry.status = "running"
    entry.pid = 1  # fake PID

    # Mock is_running to return True
    with patch.object(state, "is_running", return_value=True):
        scheduler.run_phase("periodic")
    mock_executor.run_function.assert_not_called()


def test_disabled_service_skipped(state, mock_executor, cb):
    """Disabled services should not appear in phase dispatch."""
    services = [
        ServiceConfig(
            id="active",
            phase="startup",
            order=10,
            enabled=True,
            execution={"type": "function", "function": "svc_active"},
        ),
        ServiceConfig(
            id="disabled",
            phase="startup",
            order=20,
            enabled=False,
            execution={"type": "function", "function": "svc_disabled"},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    scheduler.run_phase("startup")

    mock_executor.run_phase.assert_called_once_with("startup", ["svc_active"])


def test_condition_env_not_equals(state, mock_executor, cb):
    """Services with unmet env conditions should be skipped."""
    import os
    os.environ["WIGGUM_RUN_MODE"] = "merge-only"
    try:
        services = [
            ServiceConfig(
                id="fix",
                phase="periodic",
                order=10,
                schedule={"type": "interval", "interval": 60, "run_on_startup": False},
                execution={"type": "function", "function": "svc_fix"},
                condition={"env_not_equals": {"WIGGUM_RUN_MODE": "merge-only"}},
            ),
        ]
        scheduler = _make_scheduler(services, state, mock_executor, cb)
        scheduler._startup_complete = True
        state.get("fix").last_run = time.time() - 120

        scheduler.run_phase("periodic")
        mock_executor.run_function.assert_not_called()
    finally:
        os.environ.pop("WIGGUM_RUN_MODE", None)


# =============================================================================
# Event system tests
# =============================================================================


def test_trigger_matches_event_exact():
    """Exact pattern should match identical event."""
    assert ServiceScheduler._trigger_matches_event(
        "service.completed:foo", "service.completed:foo",
    ) is True


def test_trigger_matches_event_glob():
    """Glob suffix pattern should match events with that prefix."""
    assert ServiceScheduler._trigger_matches_event(
        "service.completed:*", "service.completed:foo",
    ) is True
    assert ServiceScheduler._trigger_matches_event(
        "service.*", "service.completed:foo",
    ) is True


def test_trigger_matches_event_no_match():
    """Non-matching pattern should return False."""
    assert ServiceScheduler._trigger_matches_event(
        "service.completed:foo", "service.completed:bar",
    ) is False
    assert ServiceScheduler._trigger_matches_event(
        "service.failed:*", "service.completed:foo",
    ) is False


def test_event_service_triggered_on_success(state, mock_executor, cb):
    """Event chain should fire after function completes with rc=0."""
    # memory-extract (interval) triggers memory-analyze (event) on success
    services = [
        ServiceConfig(
            id="memory-extract",
            phase="periodic",
            order=10,
            schedule={"type": "interval", "interval": 60, "run_on_startup": False},
            execution={"type": "function", "function": "svc_memory_extract"},
        ),
        ServiceConfig(
            id="memory-analyze",
            phase="periodic",
            order=20,
            schedule={"type": "event", "trigger": ["service.succeeded:memory-extract"]},
            execution={"type": "function", "function": "svc_memory_analyze"},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    scheduler._startup_complete = True

    # Make memory-extract due
    state.get("memory-extract").last_run = time.time() - 120

    # run_function returns 0 (success) for both calls
    mock_executor.run_function.return_value = 0

    scheduler.run_phase("periodic")

    # Both services should have been called
    calls = mock_executor.run_function.call_args_list
    called_ids = [c.args[0].id for c in calls]
    assert "memory-extract" in called_ids
    assert "memory-analyze" in called_ids


def test_event_service_triggered_on_failure(state, mock_executor, cb):
    """on_finish (service.completed:) should fire on failure too."""
    services = [
        ServiceConfig(
            id="memory-analyze",
            phase="periodic",
            order=10,
            schedule={"type": "interval", "interval": 60, "run_on_startup": False},
            execution={"type": "function", "function": "svc_memory_analyze"},
        ),
        ServiceConfig(
            id="memory-complete",
            phase="periodic",
            order=20,
            schedule={"type": "event", "trigger": ["service.completed:memory-analyze"]},
            execution={"type": "function", "function": "svc_memory_complete"},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    scheduler._startup_complete = True

    state.get("memory-analyze").last_run = time.time() - 120

    # First call (memory-analyze) fails, second call (memory-complete) succeeds
    mock_executor.run_function.side_effect = [1, 0]

    scheduler.run_phase("periodic")

    calls = mock_executor.run_function.call_args_list
    called_ids = [c.args[0].id for c in calls]
    assert "memory-analyze" in called_ids
    # service.completed fires on both success and failure
    assert "memory-complete" in called_ids


def test_event_service_conditions_checked(state, mock_executor, cb):
    """Conditions should be evaluated before running event-triggered service."""
    services = [
        ServiceConfig(
            id="extract",
            phase="periodic",
            order=10,
            schedule={"type": "interval", "interval": 60, "run_on_startup": False},
            execution={"type": "function", "function": "svc_extract"},
        ),
        ServiceConfig(
            id="analyze",
            phase="periodic",
            order=20,
            schedule={"type": "event", "trigger": ["service.succeeded:extract"]},
            execution={"type": "function", "function": "svc_analyze"},
            # Condition that won't be met: file doesn't exist
            condition={"file_exists": "/nonexistent/path/that/does/not/exist.json"},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    scheduler._startup_complete = True

    state.get("extract").last_run = time.time() - 120
    mock_executor.run_function.return_value = 0

    scheduler.run_phase("periodic")

    # Only extract should run, analyze skipped due to conditions
    calls = mock_executor.run_function.call_args_list
    called_ids = [c.args[0].id for c in calls]
    assert "extract" in called_ids
    assert "analyze" not in called_ids


def test_pipeline_exec_type(state, mock_executor, cb):
    """Pipeline exec type should call executor.run_pipeline."""
    mock_executor.run_pipeline = MagicMock(return_value=0)
    services = [
        ServiceConfig(
            id="trigger-svc",
            phase="periodic",
            order=10,
            schedule={"type": "interval", "interval": 60, "run_on_startup": False},
            execution={"type": "function", "function": "svc_trigger"},
        ),
        ServiceConfig(
            id="pipeline-svc",
            phase="periodic",
            order=20,
            schedule={"type": "event", "trigger": ["service.succeeded:trigger-svc"]},
            execution={"type": "pipeline", "pipeline": "test-pipeline"},
        ),
    ]
    scheduler = _make_scheduler(services, state, mock_executor, cb)
    scheduler._startup_complete = True

    state.get("trigger-svc").last_run = time.time() - 120
    mock_executor.run_function.return_value = 0

    scheduler.run_phase("periodic")

    mock_executor.run_pipeline.assert_called_once()
    called_svc = mock_executor.run_pipeline.call_args.args[0]
    assert called_svc.id == "pipeline-svc"
