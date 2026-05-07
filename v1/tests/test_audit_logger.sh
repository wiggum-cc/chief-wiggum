#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/utils/audit-logger.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"

TEST_DIR=""
setup() {
    TEST_DIR=$(mktemp -d)
    export PROJECT_DIR="$TEST_DIR"
    export AUDIT_LOG="$TEST_DIR/audit.log"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# Source the module under test (after setup defines AUDIT_LOG)
_source_module() {
    source "$WIGGUM_HOME/lib/utils/audit-logger.sh"
}

# =============================================================================
# init_audit_log() Tests
# =============================================================================

test_init_audit_log_creates_file_with_header() {
    _source_module
    init_audit_log

    assert_file_exists "$AUDIT_LOG" "Audit log file should be created"
    assert_file_contains "$AUDIT_LOG" "Chief Wiggum Audit Log" "Should contain header title"
    assert_file_contains "$AUDIT_LOG" "EVENT_TYPES" "Should contain event types documentation"
    assert_file_contains "$AUDIT_LOG" "TASK_ASSIGNED" "Should document TASK_ASSIGNED event"
    assert_file_contains "$AUDIT_LOG" "====" "Should contain separator line"
}

test_init_audit_log_does_not_overwrite_existing() {
    _source_module

    # Create a log with custom content
    mkdir -p "$(dirname "$AUDIT_LOG")"
    echo "EXISTING CONTENT" > "$AUDIT_LOG"

    init_audit_log

    assert_file_contains "$AUDIT_LOG" "EXISTING CONTENT" "Should preserve existing content"
    assert_file_not_contains "$AUDIT_LOG" "Chief Wiggum Audit Log" "Should not overwrite with header"
}

# =============================================================================
# audit_log() Tests
# =============================================================================

test_audit_log_writes_event_with_timestamp_and_type() {
    _source_module
    init_audit_log

    audit_log "TEST_EVENT" "key1=value1"

    # Check that the event line has a timestamp and event type
    assert_file_contains "$AUDIT_LOG" "TEST_EVENT" "Should contain event type"
    assert_file_contains "$AUDIT_LOG" "] TEST_EVENT" "Should have timestamp prefix with event type"
}

test_audit_log_writes_multiple_kvps() {
    _source_module
    init_audit_log

    audit_log "MULTI_KVP" "alpha=one" "beta=two" "gamma=three"

    assert_file_contains "$AUDIT_LOG" "alpha=one" "Should contain first kvp"
    assert_file_contains "$AUDIT_LOG" "beta=two" "Should contain second kvp"
    assert_file_contains "$AUDIT_LOG" "gamma=three" "Should contain third kvp"
    assert_file_contains "$AUDIT_LOG" "| alpha=one | beta=two | gamma=three" "Should separate kvps with pipes"
}

# =============================================================================
# audit_log_task_assigned() Tests
# =============================================================================

test_audit_log_task_assigned_correct_event_and_fields() {
    _source_module
    init_audit_log

    audit_log_task_assigned "TASK-042" "worker-TASK-042-99999" "99999"

    assert_file_contains "$AUDIT_LOG" "TASK_ASSIGNED" "Should log TASK_ASSIGNED event type"
    assert_file_contains "$AUDIT_LOG" "task_id=TASK-042" "Should include task_id"
    assert_file_contains "$AUDIT_LOG" "worker_id=worker-TASK-042-99999" "Should include worker_id"
    assert_file_contains "$AUDIT_LOG" "pid=99999" "Should include pid"
    assert_file_contains "$AUDIT_LOG" "git_user=" "Should include git_user field"
    assert_file_contains "$AUDIT_LOG" "system_user=" "Should include system_user field"
}

# =============================================================================
# audit_log_worker_start() Tests
# =============================================================================

test_audit_log_worker_start_includes_pid() {
    _source_module
    init_audit_log

    audit_log_worker_start "TASK-007" "worker-TASK-007-12345"

    assert_file_contains "$AUDIT_LOG" "WORKER_START" "Should log WORKER_START event type"
    assert_file_contains "$AUDIT_LOG" "task_id=TASK-007" "Should include task_id"
    assert_file_contains "$AUDIT_LOG" "worker_id=worker-TASK-007-12345" "Should include worker_id"
    assert_file_contains "$AUDIT_LOG" "pid=" "Should include pid field"
}

# =============================================================================
# audit_log_worker_complete() Tests
# =============================================================================

test_audit_log_worker_complete_success() {
    _source_module
    init_audit_log

    audit_log_worker_complete "TASK-010" "worker-TASK-010-55555" "COMPLETE"

    assert_file_contains "$AUDIT_LOG" "WORKER_COMPLETE" "Should log WORKER_COMPLETE for success"
    # Verify the event line does not use WORKER_FAILED
    local event_lines
    event_lines=$(grep "^\[" "$AUDIT_LOG" || true)
    local has_failed
    has_failed=$(echo "$event_lines" | grep -c "WORKER_FAILED" || true)
    assert_equals "0" "$has_failed" "Should not log WORKER_FAILED for success"
    assert_file_contains "$AUDIT_LOG" "status=COMPLETE" "Should include status=COMPLETE"
    assert_file_contains "$AUDIT_LOG" "task_id=TASK-010" "Should include task_id"
    assert_file_contains "$AUDIT_LOG" "worker_id=worker-TASK-010-55555" "Should include worker_id"
}

test_audit_log_worker_complete_failed_status() {
    _source_module
    init_audit_log

    audit_log_worker_complete "TASK-011" "worker-TASK-011-66666" "FAILED"

    assert_file_contains "$AUDIT_LOG" "WORKER_FAILED" "Should log WORKER_FAILED for non-COMPLETE status"
    assert_file_contains "$AUDIT_LOG" "status=FAILED" "Should include status=FAILED"
    assert_file_contains "$AUDIT_LOG" "task_id=TASK-011" "Should include task_id"
}

test_audit_log_worker_complete_timeout_status() {
    _source_module
    init_audit_log

    audit_log_worker_complete "TASK-012" "worker-TASK-012-77777" "TIMEOUT"

    assert_file_contains "$AUDIT_LOG" "WORKER_FAILED" "Should log WORKER_FAILED for TIMEOUT status"
    assert_file_contains "$AUDIT_LOG" "status=TIMEOUT" "Should include status=TIMEOUT"
}

# =============================================================================
# audit_log_worker_cleanup() Tests
# =============================================================================

test_audit_log_worker_cleanup_writes_event() {
    _source_module
    init_audit_log

    audit_log_worker_cleanup "TASK-020" "worker-TASK-020-88888"

    assert_file_contains "$AUDIT_LOG" "WORKER_CLEANUP" "Should log WORKER_CLEANUP event type"
    assert_file_contains "$AUDIT_LOG" "task_id=TASK-020" "Should include task_id"
    assert_file_contains "$AUDIT_LOG" "worker_id=worker-TASK-020-88888" "Should include worker_id"
    assert_file_contains "$AUDIT_LOG" "pid=" "Should include pid field"
    assert_file_contains "$AUDIT_LOG" "git_user=" "Should include git_user field"
}

# =============================================================================
# Run All Tests
# =============================================================================

# init_audit_log tests
run_test test_init_audit_log_creates_file_with_header
run_test test_init_audit_log_does_not_overwrite_existing

# audit_log tests
run_test test_audit_log_writes_event_with_timestamp_and_type
run_test test_audit_log_writes_multiple_kvps

# audit_log_task_assigned tests
run_test test_audit_log_task_assigned_correct_event_and_fields

# audit_log_worker_start tests
run_test test_audit_log_worker_start_includes_pid

# audit_log_worker_complete tests
run_test test_audit_log_worker_complete_success
run_test test_audit_log_worker_complete_failed_status
run_test test_audit_log_worker_complete_timeout_status

# audit_log_worker_cleanup tests
run_test test_audit_log_worker_cleanup_writes_event

print_test_summary
exit_with_test_result
