#!/usr/bin/env bash
# =============================================================================
# Tests for _is_terminal_failure() in lib/scheduler/scheduler.sh
#
# Covers all terminal failure classification criteria:
#   1. resume-state marks terminal (COMPLETE/ABORT)
#   2. Last pipeline step with FAIL result
#   3. NOT terminal: mid-pipeline step
#   4. NOT terminal: last step with PASS
#   5. NOT terminal: no pipeline-config.json
#   6. NOT terminal: no result file
# =============================================================================

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

TEST_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    export LOG_FILE="/dev/null"

    # Source resume-state (needed by _is_terminal_failure)
    source "$WIGGUM_HOME/lib/core/resume-state.sh"

    # Source scheduler (contains _is_terminal_failure)
    # We need to stub some dependencies first
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/core/logger.sh"

    # Stub scheduler functions not needed for these tests
    _SCHED_LOADED="${_SCHED_LOADED:-}"
    if [ -z "$_SCHED_LOADED" ]; then
        source "$WIGGUM_HOME/lib/scheduler/scheduler.sh" 2>/dev/null || true
        _SCHED_LOADED=1
    fi
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# Helper: create a worker directory with pipeline config and result
_create_worker() {
    local worker_dir="$1"
    local step_count="$2"
    local current_idx="$3"
    local current_step_id="$4"
    local gate_result="$5"

    mkdir -p "$worker_dir/results"
    mkdir -p "$worker_dir/workspace"

    # Build steps map
    local steps_json="{}"
    local i=0
    while [ "$i" -lt "$step_count" ]; do
        local sid="step-$i"
        steps_json=$(echo "$steps_json" | jq --arg id "$sid" '.[$id] = {"agent": "test-agent"}')
        ((++i))
    done

    # Write pipeline-config.json
    jq -n \
        --argjson idx "$current_idx" \
        --arg id "$current_step_id" \
        --argjson steps "$steps_json" \
        '{
            pipeline: {name: "test"},
            current: {step_idx: $idx, step_id: $id},
            steps: $steps
        }' > "$worker_dir/pipeline-config.json"

    # Write result file for current step
    if [ -n "$gate_result" ]; then
        local epoch
        epoch=$(date +%s)
        echo "{\"outputs\": {\"gate_result\": \"$gate_result\"}}" \
            > "$worker_dir/results/${epoch}-${current_step_id}-result.json"
    fi
}

# =============================================================================
# Test: Terminal when resume-state marks terminal
# =============================================================================
test_terminal_when_resume_state_terminal() {
    local worker_dir="$TEST_DIR/worker-1"
    mkdir -p "$worker_dir"

    # Write resume-state with terminal=true
    echo '{"terminal": true, "decision": "ABORT"}' > "$worker_dir/resume-state.json"

    local result=0
    _is_terminal_failure "$worker_dir" || result=$?
    assert_equals "0" "$result" "Should be terminal when resume-state.terminal=true"
}

# =============================================================================
# Test: Terminal when last pipeline step has FAIL result
# =============================================================================
test_terminal_when_last_step_fails() {
    local worker_dir="$TEST_DIR/worker-2"
    # 3 steps, current at last (idx 2), result FAIL
    _create_worker "$worker_dir" 3 2 "step-2" "FAIL"

    local result=0
    _is_terminal_failure "$worker_dir" || result=$?
    assert_equals "0" "$result" "Should be terminal when last step result is FAIL"
}

# =============================================================================
# Test: NOT terminal when mid-pipeline (not at last step)
# =============================================================================
test_not_terminal_when_mid_pipeline() {
    local worker_dir="$TEST_DIR/worker-4"
    # 3 steps, current at step 1 (not last), result FAIL
    _create_worker "$worker_dir" 3 1 "step-1" "FAIL"

    local result=0
    _is_terminal_failure "$worker_dir" || result=$?
    assert_equals "1" "$result" "Should NOT be terminal when not at last step"
}

# =============================================================================
# Test: NOT terminal when last step result is PASS
# =============================================================================
test_not_terminal_when_last_step_pass() {
    local worker_dir="$TEST_DIR/worker-5"
    # 2 steps, current at last (idx 1), result PASS
    _create_worker "$worker_dir" 2 1 "step-1" "PASS"

    local result=0
    _is_terminal_failure "$worker_dir" || result=$?
    assert_equals "1" "$result" "Should NOT be terminal when last step result is PASS"
}

# =============================================================================
# Test: NOT terminal when no pipeline-config.json
# =============================================================================
test_not_terminal_when_no_config() {
    local worker_dir="$TEST_DIR/worker-6"
    mkdir -p "$worker_dir"

    local result=0
    _is_terminal_failure "$worker_dir" || result=$?
    assert_equals "1" "$result" "Should NOT be terminal when no pipeline-config.json"
}

# =============================================================================
# Test: NOT terminal when no result file for current step
# =============================================================================
test_not_terminal_when_no_result_file() {
    local worker_dir="$TEST_DIR/worker-7"
    # Create worker but pass empty result to skip result file creation
    _create_worker "$worker_dir" 2 1 "step-1" ""

    local result=0
    _is_terminal_failure "$worker_dir" || result=$?
    assert_equals "1" "$result" "Should NOT be terminal when no result file exists"
}

# =============================================================================
# Test: NOT terminal when last step result is FIX (non-terminal)
# =============================================================================
test_not_terminal_when_last_step_fix() {
    local worker_dir="$TEST_DIR/worker-8"
    # 2 steps, current at last (idx 1), result FIX
    _create_worker "$worker_dir" 2 1 "step-1" "FIX"

    local result=0
    _is_terminal_failure "$worker_dir" || result=$?
    assert_equals "1" "$result" "Should NOT be terminal when last step result is FIX"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_terminal_when_resume_state_terminal
run_test test_terminal_when_last_step_fails
run_test test_not_terminal_when_mid_pipeline
run_test test_not_terminal_when_last_step_pass
run_test test_not_terminal_when_no_config
run_test test_not_terminal_when_no_result_file
run_test test_not_terminal_when_last_step_fix

print_test_summary
exit_with_test_result
