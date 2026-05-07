#!/usr/bin/env bash
# test_task_source.sh - Tests for distributed task source abstraction layer
set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

# =============================================================================
# Setup/Teardown
# =============================================================================

setup() {
    TEST_RALPH_DIR=$(mktemp -d)
    TEST_PROJECT_DIR=$(mktemp -d)

    # Create minimal kanban for testing
    cat > "$TEST_RALPH_DIR/kanban.md" << 'EOF'
# Kanban

## Tasks

- [ ] **[TASK-001]** First task
  - Description: A pending task
  - Priority: HIGH
  - Dependencies: none

- [x] **[TASK-002]** Completed task
  - Description: Already done
  - Priority: MEDIUM
  - Dependencies: none

- [=] **[TASK-003]** In progress task
  - Description: Currently working
  - Priority: HIGH
  - Dependencies: TASK-002

- [ ] **[TASK-004]** Blocked task
  - Description: Waiting for deps
  - Priority: LOW
  - Dependencies: TASK-001
EOF

    # Source task source after setup
    export WIGGUM_TASK_SOURCE_MODE="local"
    source "$WIGGUM_HOME/lib/tasks/task-source.sh"
}

teardown() {
    rm -rf "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"
}

# =============================================================================
# Task Source Mode Tests
# =============================================================================

test_task_source_mode_defaults_to_local() {
    unset WIGGUM_TASK_SOURCE_MODE
    # Re-source to pick up default
    _TASK_SOURCE_LOADED=""
    source "$WIGGUM_HOME/lib/tasks/task-source.sh"

    local mode
    mode=$(task_source_get_mode)
    assert_equals "local" "$mode" "Default mode should be 'local'"
}

test_task_source_mode_respects_env() {
    export WIGGUM_TASK_SOURCE_MODE="github"
    _TASK_SOURCE_LOADED=""
    source "$WIGGUM_HOME/lib/tasks/task-source.sh"

    local mode
    mode=$(task_source_get_mode)
    assert_equals "github" "$mode" "Mode should respect WIGGUM_TASK_SOURCE_MODE env"

    # Reset for other tests
    export WIGGUM_TASK_SOURCE_MODE="local"
}

# =============================================================================
# Task Source Initialization Tests
# =============================================================================

test_task_source_init_local_mode() {
    export WIGGUM_TASK_SOURCE_MODE="local"
    _TASK_SOURCE_LOADED=""
    source "$WIGGUM_HOME/lib/tasks/task-source.sh"

    assert_success "Init should succeed in local mode" \
        task_source_init "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"
}

test_task_source_init_fails_without_kanban() {
    export WIGGUM_TASK_SOURCE_MODE="local"
    _TASK_SOURCE_LOADED=""
    source "$WIGGUM_HOME/lib/tasks/task-source.sh"

    local empty_dir
    empty_dir=$(mktemp -d)

    assert_failure "Init should fail without kanban.md" \
        task_source_init "$empty_dir" "$TEST_PROJECT_DIR"

    rm -rf "$empty_dir"
}

# =============================================================================
# Task Source Get All Tasks Tests
# =============================================================================

test_task_source_get_all_tasks_returns_all() {
    task_source_init "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"

    local tasks
    tasks=$(task_source_get_all_tasks)

    assert_output_contains "$tasks" "TASK-001" "Should include TASK-001"
    assert_output_contains "$tasks" "TASK-002" "Should include TASK-002"
    assert_output_contains "$tasks" "TASK-003" "Should include TASK-003"
    assert_output_contains "$tasks" "TASK-004" "Should include TASK-004"
}

test_task_source_get_all_tasks_format() {
    task_source_init "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"

    local tasks
    tasks=$(task_source_get_all_tasks)

    # Format: task_id|status|priority|deps|owner
    local task_001
    task_001=$(echo "$tasks" | grep "^TASK-001|")

    # Should have pipe-delimited format
    local field_count
    field_count=$(echo "$task_001" | tr '|' '\n' | wc -l)

    if [ "$field_count" -ge 4 ]; then
        echo -e "  ${GREEN}✓${NC} Task format has at least 4 fields"
    else
        echo -e "  ${RED}✗${NC} Task format should have at least 4 fields, got $field_count"
        echo "    Line: $task_001"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_task_source_get_all_tasks_status_chars() {
    task_source_init "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"

    local tasks
    tasks=$(task_source_get_all_tasks)

    # Check status characters
    local pending_status in_progress_status complete_status
    pending_status=$(echo "$tasks" | grep "^TASK-001|" | cut -d'|' -f2)
    in_progress_status=$(echo "$tasks" | grep "^TASK-003|" | cut -d'|' -f2)
    complete_status=$(echo "$tasks" | grep "^TASK-002|" | cut -d'|' -f2)

    assert_equals " " "$pending_status" "Pending task should have ' ' status"
    assert_equals "=" "$in_progress_status" "In-progress task should have '=' status"
    assert_equals "x" "$complete_status" "Complete task should have 'x' status"
}

# =============================================================================
# Task Source Get Ready Tasks Tests
# =============================================================================

test_task_source_get_ready_tasks_excludes_blocked() {
    task_source_init "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"

    # Create ready-since tracking file
    local ready_since_file="$TEST_RALPH_DIR/ready-since.json"
    echo "{}" > "$ready_since_file"

    local ready_tasks
    ready_tasks=$(task_source_get_ready_tasks "$ready_since_file" 7 20000 15000 7000)

    # TASK-001 should be ready (no deps)
    assert_output_contains "$ready_tasks" "TASK-001" "TASK-001 should be ready (no deps)"

    # TASK-004 should NOT be ready (depends on TASK-001 which is pending)
    if echo "$ready_tasks" | grep -q "TASK-004"; then
        echo -e "  ${RED}✗${NC} TASK-004 should NOT be ready (blocked by TASK-001)"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} TASK-004 correctly excluded (blocked)"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_task_source_get_ready_tasks_excludes_complete() {
    task_source_init "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"

    local ready_since_file="$TEST_RALPH_DIR/ready-since.json"
    echo "{}" > "$ready_since_file"

    local ready_tasks
    ready_tasks=$(task_source_get_ready_tasks "$ready_since_file" 7 20000 15000 7000)

    # TASK-002 should NOT be ready (already complete)
    if echo "$ready_tasks" | grep -q "TASK-002"; then
        echo -e "  ${RED}✗${NC} TASK-002 should NOT be ready (already complete)"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} TASK-002 correctly excluded (complete)"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_task_source_get_ready_tasks_excludes_in_progress() {
    task_source_init "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"

    local ready_since_file="$TEST_RALPH_DIR/ready-since.json"
    echo "{}" > "$ready_since_file"

    local ready_tasks
    ready_tasks=$(task_source_get_ready_tasks "$ready_since_file" 7 20000 15000 7000)

    # TASK-003 should NOT be ready (already in progress)
    if echo "$ready_tasks" | grep -q "TASK-003"; then
        echo -e "  ${RED}✗${NC} TASK-003 should NOT be ready (already in progress)"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} TASK-003 correctly excluded (in progress)"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Task Source Status Operations Tests
# =============================================================================

test_task_source_set_status_updates_kanban() {
    task_source_init "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"

    # Set TASK-001 to in-progress
    task_source_set_status "TASK-001" "="

    # Verify in kanban
    if grep -q '\[=\].*\[TASK-001\]' "$TEST_RALPH_DIR/kanban.md"; then
        echo -e "  ${GREEN}✓${NC} TASK-001 status updated to in-progress"
    else
        echo -e "  ${RED}✗${NC} TASK-001 status not updated in kanban"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Task Source Claim/Release Tests (Local Mode - Always Succeeds)
# =============================================================================

test_task_source_claim_task_local_mode() {
    task_source_init "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"

    # In local mode, claiming always succeeds
    assert_success "Claim should succeed in local mode" \
        task_source_claim_task "TASK-001"
}

test_task_source_release_task_local_mode() {
    task_source_init "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"

    # In local mode, releasing always succeeds
    assert_success "Release should succeed in local mode" \
        task_source_release_task "TASK-001"
}

test_task_source_is_claimable_local_mode() {
    task_source_init "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"

    # In local mode, all tasks are claimable
    assert_success "All tasks claimable in local mode" \
        task_source_is_claimable "TASK-001"
}

# =============================================================================
# Task Source Server ID Tests
# =============================================================================

test_task_source_get_server_id_local_mode() {
    task_source_init "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"

    local server_id
    server_id=$(task_source_get_server_id)

    # In local mode, server_id should be "local"
    assert_equals "local" "$server_id" "Server ID should be 'local' in local mode"
}

# =============================================================================
# Run Tests
# =============================================================================

echo "=== Task Source Abstraction Tests ==="
run_test test_task_source_mode_defaults_to_local
run_test test_task_source_mode_respects_env
run_test test_task_source_init_local_mode
run_test test_task_source_init_fails_without_kanban
run_test test_task_source_get_all_tasks_returns_all
run_test test_task_source_get_all_tasks_format
run_test test_task_source_get_all_tasks_status_chars
run_test test_task_source_get_ready_tasks_excludes_blocked
run_test test_task_source_get_ready_tasks_excludes_complete
run_test test_task_source_get_ready_tasks_excludes_in_progress
run_test test_task_source_set_status_updates_kanban
run_test test_task_source_claim_task_local_mode
run_test test_task_source_release_task_local_mode
run_test test_task_source_is_claimable_local_mode
run_test test_task_source_get_server_id_local_mode

print_test_summary
exit_with_test_result
