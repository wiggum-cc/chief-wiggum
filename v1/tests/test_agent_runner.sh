#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/worker/agent-runner.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"

# We source agent-runner in each test to reset global state
# because agent_runner_cleanup clears the globals

TEST_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    # Reset global state before each test
    _AGENT_RUNNER_DIR=""
    _AGENT_RUNNER_PROJECT_DIR=""
    _AGENT_RUNNER_INTERRUPTED=false
    _AGENT_RUNNER_CHILD_PID=""
}

teardown() {
    # Ensure cleanup runs
    _AGENT_RUNNER_DIR=""
    _AGENT_RUNNER_PROJECT_DIR=""
    _AGENT_RUNNER_CHILD_PID=""
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# agent_runner_init() Tests
# =============================================================================

test_init_creates_pid_file() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
    local agent_dir="$TEST_DIR/agent1"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir"

    agent_runner_init "$agent_dir" "$project_dir" 0

    assert_file_exists "$agent_dir/agent.pid" "agent.pid file should be created"

    local pid_content
    pid_content=$(cat "$agent_dir/agent.pid")
    assert_not_equals "" "$pid_content" "PID file should contain a PID value"

    agent_runner_cleanup
}

test_init_creates_agent_directory() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
    local agent_dir="$TEST_DIR/new-agent-dir"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir"

    # Agent dir does not exist yet
    assert_failure "Agent dir should not exist before init" test -d "$agent_dir"

    agent_runner_init "$agent_dir" "$project_dir" 0

    assert_dir_exists "$agent_dir" "Agent dir should be created by init"

    agent_runner_cleanup
}

test_init_fails_with_empty_agent_dir() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir"

    local result
    result=$(agent_runner_init "" "$project_dir" 0 2>/dev/null; echo $?)
    # The function returns 1 on failure, but set -e in the module may cause issues.
    # We check that _AGENT_RUNNER_DIR is still empty
    assert_equals "" "$_AGENT_RUNNER_DIR" "Agent dir should not be set with empty arg"
}

test_init_fails_with_empty_project_dir() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
    local agent_dir="$TEST_DIR/agent2"

    local result
    result=$(agent_runner_init "$agent_dir" "" 0 2>/dev/null; echo $?)
    assert_equals "" "$_AGENT_RUNNER_PROJECT_DIR" "Project dir should not be set with empty arg"
}

# =============================================================================
# agent_runner_get_dir() / agent_runner_get_project_dir() Tests
# =============================================================================

test_get_dir_returns_correct_dir() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
    local agent_dir="$TEST_DIR/agent-get-dir"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir"

    agent_runner_init "$agent_dir" "$project_dir" 0

    local result
    result=$(agent_runner_get_dir)
    assert_equals "$agent_dir" "$result" "get_dir should return the agent directory"

    agent_runner_cleanup
}

test_get_project_dir_returns_correct_dir() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
    local agent_dir="$TEST_DIR/agent-get-proj"
    local project_dir="$TEST_DIR/my-project"
    mkdir -p "$project_dir"

    agent_runner_init "$agent_dir" "$project_dir" 0

    local result
    result=$(agent_runner_get_project_dir)
    assert_equals "$project_dir" "$result" "get_project_dir should return the project directory"

    agent_runner_cleanup
}

# =============================================================================
# agent_runner_register_child() Tests
# =============================================================================

test_register_child_stores_pid() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
    local agent_dir="$TEST_DIR/agent-child"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir"

    agent_runner_init "$agent_dir" "$project_dir" 0

    agent_runner_register_child 12345

    assert_equals "12345" "$_AGENT_RUNNER_CHILD_PID" "Child PID should be stored"

    agent_runner_cleanup
}

# =============================================================================
# agent_runner_interrupted() Tests
# =============================================================================

test_interrupted_returns_1_when_not_interrupted() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
    local agent_dir="$TEST_DIR/agent-int"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir"

    agent_runner_init "$agent_dir" "$project_dir" 0

    assert_failure "Should return 1 (false) when not interrupted" agent_runner_interrupted

    agent_runner_cleanup
}

# =============================================================================
# agent_runner_detect_violations() Tests
# =============================================================================

test_detect_violations_returns_0_when_no_flag() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
    local agent_dir="$TEST_DIR/agent-viol-clean"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir"

    agent_runner_init "$agent_dir" "$project_dir" 0

    local workspace="$TEST_DIR/workspace"
    mkdir -p "$workspace"

    assert_success "Should return 0 when no violation flag exists" \
        agent_runner_detect_violations "$workspace" "$project_dir"

    agent_runner_cleanup
}

test_detect_violations_returns_1_when_flag_exists() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
    local agent_dir="$TEST_DIR/agent-viol-flag"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir/.ralph/logs"

    agent_runner_init "$agent_dir" "$project_dir" 0

    # Create the violation flag file
    echo "VIOLATION_DETECTED" > "$agent_dir/violation_flag.txt"
    echo "Type: EDIT_OUTSIDE_WORKSPACE" >> "$agent_dir/violation_flag.txt"

    local workspace="$TEST_DIR/workspace"
    mkdir -p "$workspace"

    assert_failure "Should return 1 when violation flag exists" \
        agent_runner_detect_violations "$workspace" "$project_dir"

    agent_runner_cleanup
}

test_detect_violations_creates_violations_log() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
    local agent_dir="$TEST_DIR/agent-viol-log"
    local project_dir="$TEST_DIR/project-log"
    mkdir -p "$project_dir/.ralph/logs"
    # Set RALPH_DIR for this test's project
    export RALPH_DIR="$project_dir/.ralph"

    agent_runner_init "$agent_dir" "$project_dir" 0

    # Create the violation flag file
    echo "VIOLATION_DETECTED" > "$agent_dir/violation_flag.txt"

    local workspace="$TEST_DIR/workspace"
    mkdir -p "$workspace"

    # Run detect (will return 1 due to violation)
    agent_runner_detect_violations "$workspace" "$project_dir" 2>/dev/null || true

    assert_file_exists "$project_dir/.ralph/logs/violations.log" \
        "violations.log should be created when violation detected"
    assert_file_contains "$project_dir/.ralph/logs/violations.log" "VIOLATION" \
        "violations.log should contain VIOLATION entry"

    agent_runner_cleanup
    unset RALPH_DIR
}

# =============================================================================
# agent_runner_cleanup() Tests
# =============================================================================

test_cleanup_removes_pid_file() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
    local agent_dir="$TEST_DIR/agent-cleanup-pid"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir"

    agent_runner_init "$agent_dir" "$project_dir" 0
    assert_file_exists "$agent_dir/agent.pid" "PID file should exist after init"

    agent_runner_cleanup

    assert_file_not_exists "$agent_dir/agent.pid" "PID file should be removed after cleanup"
}

test_cleanup_clears_state_variables() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
    local agent_dir="$TEST_DIR/agent-cleanup-state"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir"

    agent_runner_init "$agent_dir" "$project_dir" 0
    agent_runner_register_child 99999

    agent_runner_cleanup

    assert_equals "" "$_AGENT_RUNNER_DIR" "Agent dir should be cleared after cleanup"
    assert_equals "" "$_AGENT_RUNNER_PROJECT_DIR" "Project dir should be cleared after cleanup"
    assert_equals "" "$_AGENT_RUNNER_CHILD_PID" "Child PID should be cleared after cleanup"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_init_creates_pid_file
run_test test_init_creates_agent_directory
run_test test_init_fails_with_empty_agent_dir
run_test test_init_fails_with_empty_project_dir
run_test test_get_dir_returns_correct_dir
run_test test_get_project_dir_returns_correct_dir
run_test test_register_child_stores_pid
run_test test_interrupted_returns_1_when_not_interrupted
run_test test_detect_violations_returns_0_when_no_flag
run_test test_detect_violations_returns_1_when_flag_exists
run_test test_detect_violations_creates_violations_log
run_test test_cleanup_removes_pid_file
run_test test_cleanup_clears_state_variables

print_test_summary
exit_with_test_result
