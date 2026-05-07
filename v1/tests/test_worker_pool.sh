#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/scheduler/worker-pool.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/scheduler/worker-pool.sh"

# Create temp dir for test isolation
TEST_DIR=""
RALPH_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    mkdir -p "$RALPH_DIR/workers"
    mkdir -p "$RALPH_DIR/orchestrator"
    pool_init
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# pool_init() Tests
# =============================================================================

test_pool_init_clears_pool() {
    pool_add "1234" "main" "TASK-001"
    pool_init

    local count
    count=$(pool_count)
    assert_equals "0" "$count" "Pool should be empty after init"
}

# =============================================================================
# pool_add() Tests
# =============================================================================

test_pool_add_success() {
    pool_add "1234" "main" "TASK-001"

    local count
    count=$(pool_count)
    assert_equals "1" "$count" "Pool should have 1 worker"
}

test_pool_add_fix_worker() {
    pool_add "1234" "fix" "TASK-001"

    local type
    type=$(pool_get_type "1234")
    assert_equals "fix" "$type" "Worker type should be fix"
}

test_pool_add_resolve_worker() {
    pool_add "1234" "resolve" "TASK-001"

    local type
    type=$(pool_get_type "1234")
    assert_equals "resolve" "$type" "Worker type should be resolve"
}

test_pool_add_invalid_type_fails() {
    local result=0
    pool_add "1234" "invalid" "TASK-001" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Adding invalid type should fail"
}

test_pool_add_duplicate_fails() {
    pool_add "1234" "main" "TASK-001"
    local result=0
    pool_add "1234" "main" "TASK-002" || result=$?

    assert_equals "1" "$result" "Adding duplicate PID should fail"
}

# =============================================================================
# pool_remove() Tests
# =============================================================================

test_pool_remove_success() {
    pool_add "1234" "main" "TASK-001"
    pool_remove "1234"

    local count
    count=$(pool_count)
    assert_equals "0" "$count" "Pool should be empty after remove"
}

test_pool_remove_nonexistent_fails() {
    local result=0
    pool_remove "9999" || result=$?

    assert_equals "1" "$result" "Removing nonexistent PID should fail"
}

# =============================================================================
# pool_get() Tests
# =============================================================================

test_pool_get_returns_info() {
    pool_add "1234" "main" "TASK-001"

    local info
    info=$(pool_get "1234")
    assert_output_contains "$info" "main" "Should contain worker type"
    assert_output_contains "$info" "TASK-001" "Should contain task_id"
}

test_pool_get_nonexistent_fails() {
    local result=0
    pool_get "9999" || result=$?

    assert_equals "1" "$result" "Getting nonexistent PID should fail"
}

# =============================================================================
# pool_get_type() Tests
# =============================================================================

test_pool_get_type_main() {
    pool_add "1234" "main" "TASK-001"

    local type
    type=$(pool_get_type "1234")
    assert_equals "main" "$type" "Type should be main"
}

test_pool_get_type_fix() {
    pool_add "1234" "fix" "TASK-001"

    local type
    type=$(pool_get_type "1234")
    assert_equals "fix" "$type" "Type should be fix"
}

# =============================================================================
# pool_get_task_id() Tests
# =============================================================================

test_pool_get_task_id() {
    pool_add "1234" "main" "TASK-001"

    local task_id
    task_id=$(pool_get_task_id "1234")
    assert_equals "TASK-001" "$task_id" "Task ID should match"
}

# =============================================================================
# pool_get_start_time() Tests
# =============================================================================

test_pool_get_start_time_is_recent() {
    local before_add
    before_add=$(date +%s)

    pool_add "1234" "main" "TASK-001"

    local start_time
    start_time=$(pool_get_start_time "1234")

    # Start time should be within 1 second of when we added it
    assert_greater_than "$start_time" "$((before_add - 1))" "Start time should be recent"
}

# =============================================================================
# pool_count() Tests
# =============================================================================

test_pool_count_all() {
    pool_add "1000" "main" "TASK-001"
    pool_add "1001" "fix" "TASK-002"
    pool_add "1002" "resolve" "TASK-003"

    local count
    count=$(pool_count)
    assert_equals "3" "$count" "Total count should be 3"
}

test_pool_count_by_type() {
    pool_add "1000" "main" "TASK-001"
    pool_add "1001" "main" "TASK-002"
    pool_add "1002" "fix" "TASK-003"

    local main_count fix_count
    main_count=$(pool_count "main")
    fix_count=$(pool_count "fix")

    assert_equals "2" "$main_count" "Main count should be 2"
    assert_equals "1" "$fix_count" "Fix count should be 1"
}

test_pool_count_empty_type() {
    pool_add "1000" "main" "TASK-001"

    local resolve_count
    resolve_count=$(pool_count "resolve")
    assert_equals "0" "$resolve_count" "Resolve count should be 0"
}

# =============================================================================
# pool_has_capacity() Tests
# =============================================================================

test_pool_has_capacity_true() {
    pool_add "1000" "main" "TASK-001"
    pool_add "1001" "main" "TASK-002"

    assert_success "Should have capacity" pool_has_capacity "main" 4
}

test_pool_has_capacity_false() {
    pool_add "1000" "main" "TASK-001"
    pool_add "1001" "main" "TASK-002"

    assert_failure "Should be at capacity" pool_has_capacity "main" 2
}

# =============================================================================
# pool_pids() Tests
# =============================================================================

test_pool_pids_all() {
    pool_add "1000" "main" "TASK-001"
    pool_add "1001" "fix" "TASK-002"

    local pids
    pids=$(pool_pids)
    assert_output_contains "$pids" "1000" "Should contain first PID"
    assert_output_contains "$pids" "1001" "Should contain second PID"
}

test_pool_pids_by_type() {
    pool_add "1000" "main" "TASK-001"
    pool_add "1001" "fix" "TASK-002"

    local main_pids
    main_pids=$(pool_pids "main")
    assert_output_contains "$main_pids" "1000" "Should contain main PID"
    assert_output_not_contains "$main_pids" "1001" "Should not contain fix PID"
}

# =============================================================================
# pool_has_task() Tests
# =============================================================================

test_pool_has_task_found() {
    pool_add "1234" "main" "TASK-001"

    local pid
    pid=$(pool_has_task "TASK-001")
    assert_equals "1234" "$pid" "Should return PID of matching task"
}

test_pool_has_task_not_found() {
    pool_add "1234" "main" "TASK-001"

    local result=0
    pool_has_task "TASK-999" || result=$?
    assert_equals "1" "$result" "Should fail when task not found"
}

# =============================================================================
# pool_foreach() Tests
# =============================================================================

test_pool_foreach_all() {
    pool_add "1000" "main" "TASK-001"
    pool_add "1001" "fix" "TASK-002"

    local count=0
    _count_callback() {
        ((++count)) || true
    }
    pool_foreach "all" _count_callback

    assert_equals "2" "$count" "Should iterate over all workers"
}

test_pool_foreach_by_type() {
    pool_add "1000" "main" "TASK-001"
    pool_add "1001" "main" "TASK-002"
    pool_add "1002" "fix" "TASK-003"

    local count=0
    _count_callback() {
        ((++count)) || true
    }
    pool_foreach "main" _count_callback

    assert_equals "2" "$count" "Should iterate over main workers only"
}

# =============================================================================
# pool_dump() Tests
# =============================================================================

test_pool_dump_format() {
    pool_add "1234" "main" "TASK-001"

    local dump
    dump=$(pool_dump)
    assert_output_contains "$dump" "1234" "Dump should contain PID"
    assert_output_contains "$dump" "main" "Dump should contain type"
    assert_output_contains "$dump" "TASK-001" "Dump should contain task_id"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_pool_init_clears_pool
run_test test_pool_add_success
run_test test_pool_add_fix_worker
run_test test_pool_add_resolve_worker
run_test test_pool_add_invalid_type_fails
run_test test_pool_add_duplicate_fails
run_test test_pool_remove_success
run_test test_pool_remove_nonexistent_fails
run_test test_pool_get_returns_info
run_test test_pool_get_nonexistent_fails
run_test test_pool_get_type_main
run_test test_pool_get_type_fix
run_test test_pool_get_task_id
run_test test_pool_get_start_time_is_recent
run_test test_pool_count_all
run_test test_pool_count_by_type
run_test test_pool_count_empty_type
run_test test_pool_has_capacity_true
run_test test_pool_has_capacity_false
run_test test_pool_pids_all
run_test test_pool_pids_by_type
run_test test_pool_has_task_found
run_test test_pool_has_task_not_found
run_test test_pool_foreach_all
run_test test_pool_foreach_by_type
run_test test_pool_dump_format

print_test_summary
exit_with_test_result
