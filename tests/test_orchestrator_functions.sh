#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/scheduler/orch-resume-decide.sh
#
# Tests _step_has_result() and _resume_decide_handle_abort() which were
# extracted from orchestrator-functions.sh into orch-resume-decide.sh.

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

# Stub dependencies that orch-resume-decide.sh references at call time
# (These are normally provided by orchestrator-functions.sh and scheduler.sh)
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/core/safe-path.sh"

# Stub functions called by _resume_decide_handle_abort
resume_state_increment() { :; }
resume_state_set_terminal() { :; }
update_kanban_failed() { :; }
github_issue_sync_task_status() { :; }
activity_log() { :; }
scheduler_mark_event() { :; }

# Source the module under test
source "$WIGGUM_HOME/lib/scheduler/orch-resume-decide.sh"

TEST_DIR=""
RALPH_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    export RALPH_DIR
    mkdir -p "$RALPH_DIR/orchestrator"
    mkdir -p "$RALPH_DIR/workers"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# _step_has_result() Tests
# =============================================================================

test_step_has_result_true_when_result_exists() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-1234567890"
    mkdir -p "$worker_dir/results"
    echo '{"gate_result":"PASS"}' > "$worker_dir/results/1234-execution-result.json"

    local exit_code=0
    _step_has_result "$worker_dir" "execution" || exit_code=$?
    assert_equals "0" "$exit_code" "Should return 0 when result file exists"
}

test_step_has_result_false_when_no_results_dir() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-1234567890"
    mkdir -p "$worker_dir"

    local exit_code=0
    _step_has_result "$worker_dir" "execution" || exit_code=$?
    assert_equals "1" "$exit_code" "Should return 1 when results dir missing"
}

test_step_has_result_false_when_no_matching_file() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-1234567890"
    mkdir -p "$worker_dir/results"
    echo '{"gate_result":"PASS"}' > "$worker_dir/results/1234-planning-result.json"

    local exit_code=0
    _step_has_result "$worker_dir" "execution" || exit_code=$?
    assert_equals "1" "$exit_code" "Should return 1 when no matching step result"
}

test_step_has_result_picks_latest_when_multiple() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-1234567890"
    mkdir -p "$worker_dir/results"
    echo '{"gate_result":"FAIL"}' > "$worker_dir/results/0001-execution-result.json"
    echo '{"gate_result":"PASS"}' > "$worker_dir/results/0002-execution-result.json"

    local exit_code=0
    _step_has_result "$worker_dir" "execution" || exit_code=$?
    assert_equals "0" "$exit_code" "Should return 0 when multiple result files exist"
}

test_step_has_result_false_when_results_dir_empty() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-1234567890"
    mkdir -p "$worker_dir/results"

    local exit_code=0
    _step_has_result "$worker_dir" "execution" || exit_code=$?
    assert_equals "1" "$exit_code" "Should return 1 when results dir is empty"
}

# =============================================================================
# _resume_decide_handle_abort() Tests
# =============================================================================

test_handle_abort_removes_decision_file() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-1234567890"
    mkdir -p "$worker_dir"
    echo '{}' > "$worker_dir/resume-decision.json"

    _resume_decide_handle_abort "$worker_dir" "TASK-001" "test abort"

    assert_file_not_exists "$worker_dir/resume-decision.json" \
        "resume-decision.json should be removed after abort"
}

test_handle_abort_calls_kanban_failed() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-1234567890"
    mkdir -p "$worker_dir"

    # Create kanban.md for update_kanban_failed
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
# Kanban

## Pending Approval

- [P] **[TASK-001]** Test task
  - Description: Test
  - Priority: HIGH
  - Dependencies: none
EOF

    # Track calls
    local _kanban_failed_called=""
    update_kanban_failed() { _kanban_failed_called="$2"; }

    _resume_decide_handle_abort "$worker_dir" "TASK-001" "test abort"

    assert_equals "TASK-001" "$_kanban_failed_called" \
        "update_kanban_failed should be called with task_id"
}

test_handle_abort_uses_default_reason() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-1234567890"
    mkdir -p "$worker_dir"

    # Track the reason passed to resume_state_increment
    local _captured_reason=""
    resume_state_increment() { _captured_reason="$5"; }

    _resume_decide_handle_abort "$worker_dir" "TASK-001"

    assert_output_contains "$_captured_reason" "auto-aborted" \
        "Default reason should include 'auto-aborted'"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_step_has_result_true_when_result_exists
run_test test_step_has_result_false_when_no_results_dir
run_test test_step_has_result_false_when_no_matching_file
run_test test_step_has_result_picks_latest_when_multiple
run_test test_step_has_result_false_when_results_dir_empty
run_test test_handle_abort_removes_decision_file
run_test test_handle_abort_calls_kanban_failed
run_test test_handle_abort_uses_default_reason

print_test_summary
exit_with_test_result
