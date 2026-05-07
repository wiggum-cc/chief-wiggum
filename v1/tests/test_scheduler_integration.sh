#!/usr/bin/env bash
# test_scheduler_integration.sh - Tests for distributed scheduler integration
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

- [ ] **[TASK-003]** Second pending task
  - Description: Another pending task
  - Priority: MEDIUM
  - Dependencies: TASK-002
EOF

    mkdir -p "$TEST_RALPH_DIR/workers"

    # Source scheduler first (required by scheduler-integration)
    source "$WIGGUM_HOME/lib/scheduler/scheduler.sh"
    # Source scheduler integration
    source "$WIGGUM_HOME/lib/distributed/scheduler-integration.sh"
}

teardown() {
    rm -rf "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR"
}

# =============================================================================
# Local Mode Tests (Backward Compatibility)
# =============================================================================

test_scheduler_init_local_mode() {
    export WIGGUM_TASK_SOURCE_MODE="local"

    assert_success "Init should succeed in local mode" \
        scheduler_init_with_task_source "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR" \
            7 20000 15000 7000 20000 8000
}

test_scheduler_tick_local_mode() {
    export WIGGUM_TASK_SOURCE_MODE="local"

    scheduler_init_with_task_source "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR" \
        7 20000 15000 7000 20000 8000

    assert_success "Tick should succeed in local mode" \
        scheduler_tick_distributed
}

test_scheduler_claim_task_local_mode() {
    export WIGGUM_TASK_SOURCE_MODE="local"

    scheduler_init_with_task_source "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR" \
        7 20000 15000 7000 20000 8000

    # In local mode, claiming always succeeds
    assert_success "Claim should succeed in local mode" \
        scheduler_claim_task "TASK-001"
}

test_scheduler_release_task_local_mode() {
    export WIGGUM_TASK_SOURCE_MODE="local"

    scheduler_init_with_task_source "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR" \
        7 20000 15000 7000 20000 8000

    # In local mode, releasing always succeeds
    assert_success "Release should succeed in local mode" \
        scheduler_release_task "TASK-001"
}

test_scheduler_verify_ownership_local_mode() {
    export WIGGUM_TASK_SOURCE_MODE="local"

    scheduler_init_with_task_source "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR" \
        7 20000 15000 7000 20000 8000

    # In local mode, ownership verification always succeeds
    assert_success "Verify ownership should succeed in local mode" \
        scheduler_verify_ownership "TASK-001"
}

test_scheduler_set_task_status_local_mode() {
    export WIGGUM_TASK_SOURCE_MODE="local"

    scheduler_init_with_task_source "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR" \
        7 20000 15000 7000 20000 8000

    # Set status to in-progress
    scheduler_set_task_status "TASK-001" "="

    # Verify in kanban
    if grep -q '\[=\].*\[TASK-001\]' "$TEST_RALPH_DIR/kanban.md"; then
        echo -e "  ${GREEN}✓${NC} Status updated in kanban"
    else
        echo -e "  ${RED}✗${NC} Status not updated in kanban"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Heartbeat Service Integration Tests (Local Mode - No-op)
# =============================================================================

test_scheduler_update_heartbeats_local_mode() {
    export WIGGUM_TASK_SOURCE_MODE="local"

    scheduler_init_with_task_source "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR" \
        7 20000 15000 7000 20000 8000

    # In local mode, heartbeat update is a no-op
    assert_success "Heartbeat update should succeed (no-op) in local mode" \
        scheduler_update_heartbeats
}

# =============================================================================
# Orphan Recovery Service Integration Tests (Local Mode - No-op)
# =============================================================================

test_scheduler_run_orphan_recovery_local_mode() {
    export WIGGUM_TASK_SOURCE_MODE="local"

    scheduler_init_with_task_source "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR" \
        7 20000 15000 7000 20000 8000

    # In local mode, orphan recovery is a no-op
    assert_success "Orphan recovery should succeed (no-op) in local mode" \
        scheduler_run_orphan_recovery
}

# =============================================================================
# Shutdown Tests
# =============================================================================

test_scheduler_shutdown_distributed_local_mode() {
    export WIGGUM_TASK_SOURCE_MODE="local"

    scheduler_init_with_task_source "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR" \
        7 20000 15000 7000 20000 8000

    # In local mode, shutdown is a no-op
    assert_success "Shutdown should succeed (no-op) in local mode" \
        scheduler_shutdown_distributed
}

# =============================================================================
# Can-Spawn Check Tests
# =============================================================================

test_scheduler_can_spawn_task_distributed_local_mode() {
    export WIGGUM_TASK_SOURCE_MODE="local"

    scheduler_init_with_task_source "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR" \
        7 20000 15000 7000 20000 8000

    scheduler_tick_distributed

    # In local mode with no workers, should be able to spawn
    assert_success "Can spawn task in local mode" \
        scheduler_can_spawn_task_distributed "TASK-001" 4
}

# =============================================================================
# Distributed Status Tests
# =============================================================================

test_scheduler_get_distributed_status_local_mode() {
    export WIGGUM_TASK_SOURCE_MODE="local"

    scheduler_init_with_task_source "$TEST_RALPH_DIR" "$TEST_PROJECT_DIR" \
        7 20000 15000 7000 20000 8000

    local status
    status=$(scheduler_get_distributed_status)

    # Should be valid JSON
    if echo "$status" | jq -e . > /dev/null 2>&1; then
        echo -e "  ${GREEN}✓${NC} Status is valid JSON"
    else
        echo -e "  ${RED}✗${NC} Status is not valid JSON: $status"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    # Mode should be "local"
    local mode
    mode=$(echo "$status" | jq -r '.mode')
    assert_equals "local" "$mode" "Mode should be 'local'"

    # Distributed should be false
    local distributed
    distributed=$(echo "$status" | jq -r '.distributed')
    assert_equals "false" "$distributed" "Distributed should be false"
}

# =============================================================================
# Run Tests
# =============================================================================

echo "=== Scheduler Integration Tests ==="
run_test test_scheduler_init_local_mode
run_test test_scheduler_tick_local_mode
run_test test_scheduler_claim_task_local_mode
run_test test_scheduler_release_task_local_mode
run_test test_scheduler_verify_ownership_local_mode
run_test test_scheduler_set_task_status_local_mode
run_test test_scheduler_update_heartbeats_local_mode
run_test test_scheduler_run_orphan_recovery_local_mode
run_test test_scheduler_shutdown_distributed_local_mode
run_test test_scheduler_can_spawn_task_distributed_local_mode
run_test test_scheduler_get_distributed_status_local_mode

print_test_summary
exit_with_test_result
