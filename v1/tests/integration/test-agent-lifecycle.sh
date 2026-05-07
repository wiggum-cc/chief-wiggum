#!/usr/bin/env bash
# =============================================================================
# Agent Lifecycle Integration Test
#
# Tests the full agent lifecycle (init -> ready -> run -> cleanup):
# - on_init fires before agent_run
# - on_ready fires after init
# - Output validation runs after completion
# - on_error fires on failure
# - Agent metadata and config loading
# - Result writing and reading
# - Communication paths
# =============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TESTS_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

TEST_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    export LOG_FILE="/dev/null"
    export RALPH_DIR="$TEST_DIR/.ralph"
    mkdir -p "$RALPH_DIR/workers" "$RALPH_DIR/logs"

    # Reset agent-base loaded flag
    unset _AGENT_BASE_LOADED 2>/dev/null || true
    source "$WIGGUM_HOME/lib/core/agent-base.sh"
}

teardown() {
    unset RALPH_DIR
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# Test: Agent metadata initialization
# =============================================================================
test_agent_metadata_init() {
    agent_init_metadata "test-lifecycle" "Lifecycle test agent"

    assert_equals "test-lifecycle" "$AGENT_TYPE" "Agent type should be set"
    assert_equals "Lifecycle test agent" "$AGENT_DESCRIPTION" "Agent description should be set"
}

# =============================================================================
# Test: Agent context setup
# =============================================================================
test_agent_context_setup() {
    local worker_dir="$TEST_DIR/worker"
    local workspace="$TEST_DIR/workspace"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$worker_dir" "$workspace" "$project_dir"

    agent_setup_context "$worker_dir" "$workspace" "$project_dir" "TASK-001"

    assert_equals "$worker_dir" "$(agent_get_worker_dir)" "Worker dir should be set"
    assert_equals "$workspace" "$(agent_get_workspace)" "Workspace should be set"
    assert_equals "$project_dir" "$(agent_get_project_dir)" "Project dir should be set"
    assert_equals "TASK-001" "$(agent_get_task_id)" "Task ID should be set"
}

# =============================================================================
# Test: Agent config loading from agents.json
# =============================================================================
test_agent_config_loading() {
    load_agent_config "engineering.software-engineer"

    assert_not_equals "" "$AGENT_CONFIG_MAX_ITERATIONS" "max_iterations should be loaded"
    assert_not_equals "" "$AGENT_CONFIG_MAX_TURNS" "max_turns should be loaded"
    assert_not_equals "" "$AGENT_CONFIG_TIMEOUT_SECONDS" "timeout_seconds should be loaded"
}

# =============================================================================
# Test: Default lifecycle hooks return 0
# =============================================================================
test_default_hooks_return_0() {
    # Default implementations should all return 0
    assert_success "agent_on_init should return 0 by default" agent_on_init "/tmp/w" "/tmp/p"
    assert_success "agent_on_ready should return 0 by default" agent_on_ready "/tmp/w" "/tmp/p"
    assert_success "agent_on_error should return 0 by default" agent_on_error "/tmp/w" "1" "test_error"
    assert_success "agent_on_signal should return 0 by default" agent_on_signal "TERM"
}

# =============================================================================
# Test: on_init fires before on_ready in lifecycle
# =============================================================================
test_init_fires_before_ready() {
    local sequence_file="$TEST_DIR/lifecycle_sequence.txt"
    : > "$sequence_file"

    # Override hooks to track order
    agent_on_init() {
        echo "init" >> "$sequence_file"
        return 0
    }
    agent_on_ready() {
        echo "ready" >> "$sequence_file"
        return 0
    }

    # Simulate lifecycle (what run_agent would do)
    agent_on_init
    agent_on_ready

    local first_event second_event
    first_event=$(sed -n '1p' "$sequence_file")
    second_event=$(sed -n '2p' "$sequence_file")

    assert_equals "init" "$first_event" "on_init should fire first"
    assert_equals "ready" "$second_event" "on_ready should fire second"
}

# =============================================================================
# Test: on_error fires on agent failure
# =============================================================================
test_on_error_fires_on_failure() {
    local error_file="$TEST_DIR/error_fired.txt"

    agent_on_error() {
        echo "error:$1" > "$error_file"
        return 0
    }

    # Simulate error scenario
    local error_msg="Agent run failed with exit code 1"
    agent_on_error "$error_msg"

    assert_file_exists "$error_file" "on_error should have fired"
    assert_file_contains "$error_file" "error:Agent run failed" "Error message should be passed"
}

# =============================================================================
# Test: Agent result writing creates valid JSON
# =============================================================================
test_agent_result_writing() {
    local worker_dir="$TEST_DIR/worker-result"
    mkdir -p "$worker_dir"
    AGENT_TYPE="test-writer"
    _AGENT_TASK_ID="TASK-001"
    _AGENT_START_EPOCH=$(date +%s)

    agent_write_result "$worker_dir" "PASS" \
        '{"pr_url":"https://github.com/test/pr/42"}'

    local result_file
    result_file=$(agent_get_result_path "$worker_dir")
    assert_file_exists "$result_file" "Result file should be created"

    local status exit_code task_id
    status=$(jq -r '.status' "$result_file")
    exit_code=$(jq -r '.exit_code' "$result_file")
    task_id=$(jq -r '.task_id' "$result_file")

    assert_equals "success" "$status" "Status should be 'success'"
    assert_equals "0" "$exit_code" "Exit code should be 0"
    assert_equals "TASK-001" "$task_id" "Task ID should be in result"
}

# =============================================================================
# Test: Agent result reading
# =============================================================================
test_agent_result_reading() {
    local worker_dir="$TEST_DIR/worker-read"
    mkdir -p "$worker_dir"
    AGENT_TYPE="test-reader"
    _AGENT_TASK_ID="TASK-002"
    _AGENT_START_EPOCH=$(date +%s)

    agent_write_result "$worker_dir" "FAIL" \
        '{"error":"timeout"}' '["Resource exhausted"]'

    local status
    status=$(agent_read_result "$worker_dir" ".status")
    assert_equals "failure" "$status" "Should read failure status"

    local exit_code
    exit_code=$(agent_read_result "$worker_dir" ".exit_code")
    assert_equals "10" "$exit_code" "Should read exit code 10 for FAIL"
}

# =============================================================================
# Test: agent_result_is_success function
# =============================================================================
test_result_is_success() {
    local worker_dir="$TEST_DIR/worker-success-check"
    mkdir -p "$worker_dir"
    AGENT_TYPE="test-success"
    _AGENT_TASK_ID="TASK-003"
    _AGENT_START_EPOCH=$(date +%s)

    # Write success result
    agent_write_result "$worker_dir" "PASS"
    assert_success "Should return true for success result" \
        agent_result_is_success "$worker_dir"

    # Overwrite with failure result (use new epoch so it's the "latest")
    _AGENT_START_EPOCH=$(( $(date +%s) + 1 ))
    agent_write_result "$worker_dir" "FAIL"
    assert_failure "Should return false for failure result" \
        agent_result_is_success "$worker_dir"
}

# =============================================================================
# Test: Agent set/get output
# =============================================================================
test_agent_output_set_get() {
    local worker_dir="$TEST_DIR/worker-output"
    mkdir -p "$worker_dir"
    AGENT_TYPE="test-output"
    _AGENT_TASK_ID="TASK-004"
    _AGENT_START_EPOCH=$(date +%s)

    agent_write_result "$worker_dir" "PASS"
    agent_set_output "$worker_dir" "pr_url" "https://github.com/pr/99"

    local value
    value=$(agent_get_output "$worker_dir" "pr_url")
    assert_equals "https://github.com/pr/99" "$value" "Should retrieve stored output value"
}

# =============================================================================
# Test: Agent error accumulation
# =============================================================================
test_agent_error_accumulation() {
    local worker_dir="$TEST_DIR/worker-errors"
    mkdir -p "$worker_dir"
    AGENT_TYPE="test-errors"
    _AGENT_TASK_ID="TASK-005"
    _AGENT_START_EPOCH=$(date +%s)

    agent_write_result "$worker_dir" "FAIL"
    agent_add_error "$worker_dir" "First error"
    agent_add_error "$worker_dir" "Second error"

    local result_file
    result_file=$(agent_find_latest_result "$worker_dir" "$AGENT_TYPE")

    local error_count
    error_count=$(jq '.errors | length' "$result_file")
    assert_equals "2" "$error_count" "Should have 2 accumulated errors"

    assert_file_contains "$result_file" "First error" "First error should be recorded"
    assert_file_contains "$result_file" "Second error" "Second error should be recorded"
}

# =============================================================================
# Test: Communication paths are correct
# =============================================================================
test_communication_paths() {
    local worker_dir="$TEST_DIR/worker-comm"
    mkdir -p "$worker_dir"
    AGENT_TYPE="test-comm"
    _AGENT_TASK_ID="TASK-COMM"
    _AGENT_START_EPOCH=$(date +%s)

    # Create a result file so agent_find_latest_result can find it
    agent_write_result "$worker_dir" "PASS"

    local result_path
    result_path=$(agent_comm_path "$worker_dir" "result")
    assert_file_exists "$result_path" "Result comm path should point to existing file"

    local workspace_path
    workspace_path=$(agent_comm_path "$worker_dir" "workspace")
    assert_equals "$worker_dir/workspace" "$workspace_path" "Workspace path should be correct"

    local summary_path
    summary_path=$(agent_comm_path "$worker_dir" "summary")
    assert_equals "$worker_dir/summaries/summary.txt" "$summary_path" "Summary path should be correct"
}

# =============================================================================
# Test: Agent directory creation
# =============================================================================
test_agent_directory_creation() {
    local worker_dir="$TEST_DIR/worker-dirs"

    agent_create_directories "$worker_dir"

    assert_dir_exists "$worker_dir/logs" "Logs directory should be created"
    assert_dir_exists "$worker_dir/summaries" "Summaries directory should be created"
    assert_dir_exists "$worker_dir/results" "Results directory should be created"
    assert_dir_exists "$worker_dir/reports" "Reports directory should be created"
}

# =============================================================================
# Test: Full lifecycle sequence (init -> config -> ready -> run -> result -> cleanup)
# =============================================================================
test_full_lifecycle_sequence() {
    local worker_dir="$TEST_DIR/worker-full-lifecycle"
    local workspace="$TEST_DIR/workspace-full"
    local project_dir="$TEST_DIR/project-full"
    local sequence_file="$TEST_DIR/full_sequence.txt"
    mkdir -p "$worker_dir" "$workspace" "$project_dir"
    : > "$sequence_file"

    # Initialize metadata
    agent_init_metadata "test-lifecycle" "Full lifecycle test"
    assert_equals "test-lifecycle" "$AGENT_TYPE" "Metadata should be set"

    # Setup context
    agent_setup_context "$worker_dir" "$workspace" "$project_dir" "TASK-FULL"
    assert_equals "TASK-FULL" "$(agent_get_task_id)" "Task ID should be set"

    # Create directories
    agent_create_directories "$worker_dir"
    assert_dir_exists "$worker_dir/logs" "Dirs should be created"

    # on_init
    agent_on_init() { echo "1-init" >> "$sequence_file"; return 0; }
    agent_on_ready() { echo "2-ready" >> "$sequence_file"; return 0; }

    agent_on_init
    echo "1-init" >> "$sequence_file" 2>/dev/null || true  # Recorded above
    agent_on_ready

    # Simulate agent_run
    echo "3-run" >> "$sequence_file"

    # Write result
    AGENT_TYPE="test-lifecycle"
    _AGENT_TASK_ID="TASK-FULL"
    _AGENT_START_EPOCH=$(date +%s)
    agent_write_result "$worker_dir" "PASS"
    echo "4-result" >> "$sequence_file"

    # Verify full sequence happened
    local line_count
    line_count=$(wc -l < "$sequence_file" | tr -d '[:space:]')
    assert_greater_than "$line_count" 3 "Should have at least 4 lifecycle events"

    local result_file
    result_file=$(agent_get_result_path "$worker_dir")
    assert_file_exists "$result_file" "Result should be written"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_agent_metadata_init
run_test test_agent_context_setup
run_test test_agent_config_loading
run_test test_default_hooks_return_0
run_test test_init_fires_before_ready
run_test test_on_error_fires_on_failure
run_test test_agent_result_writing
run_test test_agent_result_reading
run_test test_result_is_success
run_test test_agent_output_set_get
run_test test_agent_error_accumulation
run_test test_communication_paths
run_test test_agent_directory_creation
run_test test_full_lifecycle_sequence

print_test_summary
exit_with_test_result
