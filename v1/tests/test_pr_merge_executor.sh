#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/scheduler/pr-merge-data.sh — optimizer status tracking
#
# Tests pr_optimizer_is_running, pr_optimizer_mark_started,
# pr_optimizer_mark_completed, pr_optimizer_mark_failed,
# pr_optimizer_check_completion, and pr_optimizer_clear_status.

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/core/safe-path.sh"
source "$WIGGUM_HOME/lib/scheduler/pr-merge-data.sh"

TEST_DIR=""
RALPH_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    mkdir -p "$RALPH_DIR/orchestrator"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# pr_optimizer_is_running() Tests
# =============================================================================

test_is_running_false_when_no_status_file() {
    local exit_code=0
    pr_optimizer_is_running "$RALPH_DIR" || exit_code=$?
    assert_equals "1" "$exit_code" "Should return 1 when no status file"
}

test_is_running_true_when_running_with_live_pid() {
    # Use current shell PID (guaranteed alive)
    pr_optimizer_mark_started "$RALPH_DIR" "$$"

    local exit_code=0
    pr_optimizer_is_running "$RALPH_DIR" || exit_code=$?
    assert_equals "0" "$exit_code" "Should return 0 when running with live PID"
}

test_is_running_false_when_running_with_dead_pid() {
    pr_optimizer_mark_started "$RALPH_DIR" "99999"

    local exit_code=0
    pr_optimizer_is_running "$RALPH_DIR" || exit_code=$?
    assert_equals "1" "$exit_code" "Should return 1 when PID is dead"
}

test_is_running_false_when_completed() {
    pr_optimizer_mark_started "$RALPH_DIR" "$$"
    pr_optimizer_mark_completed "$RALPH_DIR" 3

    local exit_code=0
    pr_optimizer_is_running "$RALPH_DIR" || exit_code=$?
    assert_equals "1" "$exit_code" "Should return 1 when status is completed"
}

# =============================================================================
# pr_optimizer_mark_started() Tests
# =============================================================================

test_mark_started_creates_file() {
    pr_optimizer_mark_started "$RALPH_DIR" "12345"

    local status_file="$RALPH_DIR/.pr-optimizer-status.json"
    assert_file_exists "$status_file" "Status file should be created"

    local status
    status=$(jq -r '.status' "$status_file")
    assert_equals "running" "$status" "Status should be 'running'"

    local pid
    pid=$(jq -r '.pid' "$status_file")
    assert_equals "12345" "$pid" "PID should be stored"
}

test_mark_started_includes_timestamp() {
    pr_optimizer_mark_started "$RALPH_DIR" "12345"

    local status_file="$RALPH_DIR/.pr-optimizer-status.json"
    local started_at
    started_at=$(jq -r '.started_at' "$status_file")
    assert_not_empty "$started_at" "started_at should be set"
}

# =============================================================================
# pr_optimizer_mark_completed() Tests
# =============================================================================

test_mark_completed_updates_status() {
    pr_optimizer_mark_started "$RALPH_DIR" "$$"
    pr_optimizer_mark_completed "$RALPH_DIR" 5

    local status_file="$RALPH_DIR/.pr-optimizer-status.json"

    local status
    status=$(jq -r '.status' "$status_file")
    assert_equals "completed" "$status" "Status should be 'completed'"

    local merged_count
    merged_count=$(jq -r '.merged_count' "$status_file")
    assert_equals "5" "$merged_count" "merged_count should be 5"
}

test_mark_completed_includes_timestamp() {
    pr_optimizer_mark_started "$RALPH_DIR" "$$"
    pr_optimizer_mark_completed "$RALPH_DIR" 0

    local status_file="$RALPH_DIR/.pr-optimizer-status.json"
    local completed_at
    completed_at=$(jq -r '.completed_at' "$status_file")
    assert_not_empty "$completed_at" "completed_at should be set"
}

test_mark_completed_noop_without_status_file() {
    local exit_code=0
    pr_optimizer_mark_completed "$RALPH_DIR" 1 || exit_code=$?
    assert_equals "0" "$exit_code" "Should not fail when no status file"
}

# =============================================================================
# pr_optimizer_mark_failed() Tests
# =============================================================================

test_mark_failed_updates_status() {
    pr_optimizer_mark_started "$RALPH_DIR" "$$"
    pr_optimizer_mark_failed "$RALPH_DIR" "Network timeout"

    local status_file="$RALPH_DIR/.pr-optimizer-status.json"

    local status
    status=$(jq -r '.status' "$status_file")
    assert_equals "failed" "$status" "Status should be 'failed'"

    local error
    error=$(jq -r '.error' "$status_file")
    assert_equals "Network timeout" "$error" "Error should be stored"
}

# =============================================================================
# pr_optimizer_check_completion() Tests
# =============================================================================

test_check_completion_returns_merged_count() {
    pr_optimizer_mark_started "$RALPH_DIR" "$$"
    pr_optimizer_mark_completed "$RALPH_DIR" 7

    local result exit_code=0
    result=$(pr_optimizer_check_completion "$RALPH_DIR") || exit_code=$?

    assert_equals "0" "$exit_code" "Should return 0 for completed"
    assert_equals "7" "$result" "Should output merged count"
}

test_check_completion_returns_zero_on_failure() {
    pr_optimizer_mark_started "$RALPH_DIR" "$$"
    pr_optimizer_mark_failed "$RALPH_DIR" "some error"

    local result exit_code=0
    result=$(pr_optimizer_check_completion "$RALPH_DIR") || exit_code=$?

    assert_equals "0" "$exit_code" "Should return 0 for failed (still completed)"
    assert_equals "0" "$result" "Should output 0 for failed"
}

test_check_completion_returns_1_when_still_running() {
    pr_optimizer_mark_started "$RALPH_DIR" "$$"

    local exit_code=0
    pr_optimizer_check_completion "$RALPH_DIR" >/dev/null || exit_code=$?
    assert_equals "1" "$exit_code" "Should return 1 when still running"
}

test_check_completion_returns_1_when_no_file() {
    local exit_code=0
    pr_optimizer_check_completion "$RALPH_DIR" >/dev/null || exit_code=$?
    assert_equals "1" "$exit_code" "Should return 1 when no status file"
}

test_check_completion_detects_dead_process() {
    pr_optimizer_mark_started "$RALPH_DIR" "99999"

    local result exit_code=0
    result=$(pr_optimizer_check_completion "$RALPH_DIR") || exit_code=$?

    assert_equals "0" "$exit_code" "Should return 0 when process died"
    assert_equals "0" "$result" "Should output 0 for dead process"
}

# =============================================================================
# pr_optimizer_clear_status() Tests
# =============================================================================

test_clear_status_removes_file() {
    pr_optimizer_mark_started "$RALPH_DIR" "$$"
    pr_optimizer_clear_status "$RALPH_DIR"

    local status_file="$RALPH_DIR/.pr-optimizer-status.json"
    assert_file_not_exists "$status_file" "Status file should be removed"
}

test_clear_status_noop_when_no_file() {
    local exit_code=0
    pr_optimizer_clear_status "$RALPH_DIR" || exit_code=$?
    assert_equals "0" "$exit_code" "Should not fail when no status file"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_is_running_false_when_no_status_file
run_test test_is_running_true_when_running_with_live_pid
run_test test_is_running_false_when_running_with_dead_pid
run_test test_is_running_false_when_completed
run_test test_mark_started_creates_file
run_test test_mark_started_includes_timestamp
run_test test_mark_completed_updates_status
run_test test_mark_completed_includes_timestamp
run_test test_mark_completed_noop_without_status_file
run_test test_mark_failed_updates_status
run_test test_check_completion_returns_merged_count
run_test test_check_completion_returns_zero_on_failure
run_test test_check_completion_returns_1_when_still_running
run_test test_check_completion_returns_1_when_no_file
run_test test_check_completion_detects_dead_process
run_test test_clear_status_removes_file
run_test test_clear_status_noop_when_no_file

print_test_summary
exit_with_test_result
