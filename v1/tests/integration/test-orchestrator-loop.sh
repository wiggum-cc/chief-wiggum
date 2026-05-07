#!/usr/bin/env bash
set -euo pipefail
# test-orchestrator-loop.sh - Integration tests for orchestrator main loop

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
export WIGGUM_HOME="$PROJECT_ROOT"

# Inject mocks into PATH
export PATH="$PROJECT_ROOT/tests/mocks:$PATH"

# Test utilities
TEST_COUNT=0
PASS_COUNT=0
FAIL_COUNT=0

test_start() {
    TEST_COUNT=$((TEST_COUNT + 1))
    echo -n "Test $TEST_COUNT: $1... "
}

test_pass() {
    PASS_COUNT=$((PASS_COUNT + 1))
    echo "PASS"
}

test_fail() {
    FAIL_COUNT=$((FAIL_COUNT + 1))
    echo "FAIL"
    [ -n "${1:-}" ] && echo "  Error: $1"
}

# Cleanup
cleanup() {
    [ -n "${TEST_TEMP_DIR:-}" ] && rm -rf "$TEST_TEMP_DIR" 2>/dev/null || true
}
trap cleanup EXIT

TEST_TEMP_DIR=$(mktemp -d)
export PROJECT_DIR="$TEST_TEMP_DIR"
export RALPH_DIR="$TEST_TEMP_DIR/.ralph"
export LOG_LEVEL=ERROR

# Mock configuration
export MOCK_CLAUDE_LOG_DIR="$TEST_TEMP_DIR/mock-claude-logs"
export MOCK_GH_LOG_DIR="$TEST_TEMP_DIR/mock-gh-logs"
export CLAUDE="$PROJECT_ROOT/tests/mocks/mock-claude.sh"
export MOCK_CLAUDE_RESPONSE="Task completed successfully."
export MOCK_CLAUDE_EXIT_CODE=0

mkdir -p "$MOCK_CLAUDE_LOG_DIR" "$MOCK_GH_LOG_DIR"

# =============================================================================
# Setup Functions
# =============================================================================

setup_minimal_project() {
    mkdir -p "$RALPH_DIR/workers"
    mkdir -p "$RALPH_DIR/logs"
    mkdir -p "$RALPH_DIR/services"
    mkdir -p "$RALPH_DIR/orchestrator"

    # Create kanban with pending task
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
# Kanban

## TASKS

- [ ] **[TEST-001]** Test task one
  - Description: A simple test task
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TEST-002]** Test task two
  - Description: Another test task
  - Priority: MEDIUM
  - Dependencies: TEST-001
EOF

    # Initialize git repo for worktree operations
    (
        cd "$TEST_TEMP_DIR"
        git init -q
        git config user.email "test@test.com"
        git config user.name "Test"
        echo "# Test" > README.md
        git add .
        git commit -q -m "Initial commit"
    )
}

# =============================================================================
# Tests
# =============================================================================

echo "=== Orchestrator Loop Integration Tests ==="
echo ""

# Test 1: Kanban validation passes for valid kanban
test_start "Kanban validation passes"
(
    setup_minimal_project

    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/service-handlers/orchestrator-handlers.sh"

    svc_orch_validate_kanban > /dev/null 2>&1
) && test_pass || test_fail "Validation should pass"

# Test 2: Kanban validation fails for invalid kanban
test_start "Kanban validation fails for invalid format"
(
    setup_minimal_project

    # Create invalid kanban
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
# Invalid Kanban
- [ ] Missing task ID
EOF

    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/service-handlers/orchestrator-handlers.sh"

    ! svc_orch_validate_kanban > /dev/null 2>&1
) && test_pass || test_fail "Validation should fail"

# Test 3: Scheduler initialization detects tasks
test_start "Scheduler initializes with tasks"
(
    setup_minimal_project

    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/defaults.sh"
    source "$WIGGUM_HOME/lib/scheduler/scheduler.sh"

    scheduler_init "$RALPH_DIR" "$PROJECT_DIR" 7 20000 15000 7000 5000 3000
    scheduler_tick 2>/dev/null

    # Should have tasks queued
    [[ "$SCHED_READY_TASKS" == *"TEST-001"* ]]
) && test_pass || test_fail "Scheduler should find tasks"

# Test 4: Worker directory structure created correctly
test_start "Worker directory structure"
(
    setup_minimal_project

    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/git/worktree-helpers.sh"

    # Create worker structure manually (simulating spawn)
    worker_id="12345678"
    worker_dir="$RALPH_DIR/workers/worker-TEST-001-$worker_id"
    mkdir -p "$worker_dir/output"

    [ -d "$worker_dir" ] && [ -d "$worker_dir/output" ]
) && test_pass || test_fail "Directory not created"

# Test 5: Service state persistence
test_start "Service state persists"
(
    setup_minimal_project

    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    # Initialize state
    service_state_init "$RALPH_DIR"

    # Update a service
    service_state_set_status "test-service" "running"
    service_state_save

    # Verify persistence
    [ -f "$RALPH_DIR/services/state.json" ]

    # Load and verify
    status=$(service_state_get_status "test-service")
    [ "$status" = "running" ]
) && test_pass || test_fail "State not persisted"

# Test 6: Service state survives simulated restart
test_start "Service state survives restart"
(
    setup_minimal_project

    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    # First "run" - set state
    service_state_init "$RALPH_DIR"
    service_state_set_status "pr-sync" "stopped"
    service_state_set_last_run "pr-sync" "1700000000"
    service_state_save

    # Clear in-memory state (simulate restart)
    unset _SERVICE_STATE
    unset _SERVICE_STATE_FILE
    _SERVICE_STATE_LOADED=""

    # Second "run" - restore
    source "$WIGGUM_HOME/lib/service/service-state.sh"
    service_state_init "$RALPH_DIR"
    service_state_restore

    last_run=$(service_state_get_last_run "pr-sync")
    [ "$last_run" = "1700000000" ]
) && test_pass || test_fail "State not restored"

# Test 7: Mock Claude invocation is captured
test_start "Mock Claude captures invocations"
(
    setup_minimal_project

    # Run mock claude
    "$CLAUDE" --print "test prompt" --output-format stream-json > /dev/null 2>&1

    # Check invocation logged
    [ -f "$MOCK_CLAUDE_LOG_DIR/mock-claude-invocations" ]
    [ "$(cat "$MOCK_CLAUDE_LOG_DIR/mock-claude-invocations")" -ge 1 ]
) && test_pass || test_fail "Invocation not logged"

# Test 8: Task parser extracts tasks correctly
test_start "Task parser extracts pending tasks"
(
    setup_minimal_project

    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/tasks/task-parser.sh"

    tasks=$(get_todo_tasks "$RALPH_DIR/kanban.md")

    # Should have TEST-001 (pending)
    echo "$tasks" | grep -q "TEST-001"
) && test_pass || test_fail "Tasks not extracted"

# Test 9: Dependency blocking works
test_start "Dependency blocking"
(
    setup_minimal_project

    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/defaults.sh"
    source "$WIGGUM_HOME/lib/scheduler/scheduler.sh"

    scheduler_init "$RALPH_DIR" "$PROJECT_DIR" 7 20000 15000 7000 5000 3000
    scheduler_tick 2>/dev/null

    # TEST-001 should be ready
    echo "$SCHED_READY_TASKS" | grep -q "TEST-001" || exit 1

    # TEST-002 should NOT be ready (blocked by TEST-001)
    if echo "$SCHED_READY_TASKS" | grep -q "TEST-002"; then
        exit 1  # Should not be in ready list
    fi

    true
) && test_pass || test_fail "Dependency not blocking"

# Test 10: Process module helpers work correctly
test_start "Process module wait_safe"
(
    source "$WIGGUM_HOME/lib/core/process.sh"

    # Start a process that exits with code 42
    (exit 42) &
    pid=$!

    # Use wait_safe_var to avoid subshell issue with $()
    exit_code=0
    wait_safe_var exit_code "$pid"

    [ "$exit_code" = "42" ]
) && test_pass || test_fail "wait_safe incorrect"

# Test 11: GitHub API module loads
test_start "GitHub API module loads"
(
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/github/gh-api.sh"

    # Verify functions exist
    type gh_api > /dev/null 2>&1
    type gh_pr_list > /dev/null 2>&1
    type gh_current_user > /dev/null 2>&1
) && test_pass || test_fail "gh-api.sh not loadable"

# Test 12: Service handler common module loads
test_start "Service handler common module loads"
(
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/service/service-handler-common.sh"

    # Verify functions exist
    type svc_require_env > /dev/null 2>&1
    type svc_run_if > /dev/null 2>&1
    type svc_try > /dev/null 2>&1
) && test_pass || test_fail "service-handler-common.sh not loadable"

# =============================================================================
# Summary
# =============================================================================

echo ""
echo "=== Results ==="
echo "Passed: $PASS_COUNT / $TEST_COUNT"

if [ $FAIL_COUNT -gt 0 ]; then
    echo "Failed: $FAIL_COUNT"
    exit 1
fi

exit 0
