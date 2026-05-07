#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/scheduler/priority-workers.sh
#
# Tests capacity management (_priority_capacity_init/reserve/release/sync),
# _verify_task_merged, and recover_failed_workers.

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"

# Stub external functions that priority-workers.sh calls
update_kanban_failed() { :; }
github_issue_sync_task_status() { :; }
get_task_status() { echo "P"; }
get_task_id_from_worker() { echo "$1" | sed 's/worker-\([A-Za-z]*-[0-9]*\)-.*/\1/'; }

# Mock gh CLI
_MOCK_BIN=""

# Source the module under test (transitively sources git-state.sh, etc.)
source "$WIGGUM_HOME/lib/scheduler/priority-workers.sh"

TEST_DIR=""
RALPH_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    export RALPH_DIR
    mkdir -p "$RALPH_DIR/workers"
    mkdir -p "$RALPH_DIR/orchestrator"

    # Mock gh to avoid real GitHub API calls
    _MOCK_BIN="$TEST_DIR/mock-bin"
    mkdir -p "$_MOCK_BIN"
    cat > "$_MOCK_BIN/gh" << 'EOF'
#!/usr/bin/env bash
echo "UNKNOWN"
EOF
    chmod +x "$_MOCK_BIN/gh"
    export PATH="$_MOCK_BIN:$PATH"
    export WIGGUM_GH_TIMEOUT=1
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# _priority_capacity_init() Tests
# =============================================================================

test_capacity_init_creates_file() {
    _priority_capacity_init "$RALPH_DIR"

    assert_file_exists "$RALPH_DIR/orchestrator/priority-worker-count" \
        "Capacity file should be created"
}

test_capacity_init_sets_zero() {
    _priority_capacity_init "$RALPH_DIR"

    local count
    count=$(cat "$RALPH_DIR/orchestrator/priority-worker-count")
    assert_equals "0" "$count" "Initial count should be 0"
}

test_capacity_init_preserves_existing() {
    mkdir -p "$RALPH_DIR/orchestrator"
    echo "3" > "$RALPH_DIR/orchestrator/priority-worker-count"

    _priority_capacity_init "$RALPH_DIR"

    local count
    count=$(cat "$RALPH_DIR/orchestrator/priority-worker-count")
    assert_equals "3" "$count" "Existing count should be preserved"
}

# =============================================================================
# _priority_capacity_reserve() Tests
# =============================================================================

test_capacity_reserve_success_below_limit() {
    local exit_code=0
    _priority_capacity_reserve "$RALPH_DIR" 3 || exit_code=$?

    assert_equals "0" "$exit_code" "Should succeed when below limit"

    local count
    count=$(cat "$RALPH_DIR/orchestrator/priority-worker-count")
    assert_equals "1" "$count" "Count should be incremented to 1"
}

test_capacity_reserve_fails_at_limit() {
    _priority_capacity_reserve "$RALPH_DIR" 2 || true
    _priority_capacity_reserve "$RALPH_DIR" 2 || true

    local exit_code=0
    _priority_capacity_reserve "$RALPH_DIR" 2 || exit_code=$?

    assert_equals "1" "$exit_code" "Should fail when at limit"

    local count
    count=$(cat "$RALPH_DIR/orchestrator/priority-worker-count")
    assert_equals "2" "$count" "Count should stay at limit"
}

test_capacity_reserve_increments_sequentially() {
    _priority_capacity_reserve "$RALPH_DIR" 5 || true
    _priority_capacity_reserve "$RALPH_DIR" 5 || true
    _priority_capacity_reserve "$RALPH_DIR" 5 || true

    local count
    count=$(cat "$RALPH_DIR/orchestrator/priority-worker-count")
    assert_equals "3" "$count" "Count should be 3 after 3 reserves"
}

# =============================================================================
# _priority_capacity_release() Tests
# =============================================================================

test_capacity_release_decrements() {
    _priority_capacity_reserve "$RALPH_DIR" 5 || true
    _priority_capacity_reserve "$RALPH_DIR" 5 || true

    _priority_capacity_release "$RALPH_DIR"

    local count
    count=$(cat "$RALPH_DIR/orchestrator/priority-worker-count")
    assert_equals "1" "$count" "Count should be 1 after release"
}

test_capacity_release_floors_at_zero() {
    _priority_capacity_init "$RALPH_DIR"

    _priority_capacity_release "$RALPH_DIR"

    local count
    count=$(cat "$RALPH_DIR/orchestrator/priority-worker-count")
    assert_equals "0" "$count" "Count should not go below 0"
}

test_capacity_reserve_then_release_roundtrip() {
    _priority_capacity_reserve "$RALPH_DIR" 5 || true
    _priority_capacity_release "$RALPH_DIR"

    local count
    count=$(cat "$RALPH_DIR/orchestrator/priority-worker-count")
    assert_equals "0" "$count" "Reserve + release should return to 0"
}

# =============================================================================
# _priority_capacity_sync() Tests
# =============================================================================

test_capacity_sync_resets_to_zero_when_no_workers() {
    # Set count to stale value
    _priority_capacity_init "$RALPH_DIR"
    echo "5" > "$RALPH_DIR/orchestrator/priority-worker-count"

    _priority_capacity_sync "$RALPH_DIR"

    local count
    count=$(cat "$RALPH_DIR/orchestrator/priority-worker-count")
    assert_equals "0" "$count" "Should reset to 0 when no active workers"
}

test_capacity_sync_ignores_non_priority_workers() {
    # Create a worker with "none" state (main worker, not priority)
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-1234567890"
    mkdir -p "$worker_dir"
    echo '{"current_state": "none"}' > "$worker_dir/git-state.json"
    echo "99999" > "$worker_dir/agent.pid"

    echo "5" > "$RALPH_DIR/orchestrator/priority-worker-count"
    _priority_capacity_sync "$RALPH_DIR"

    local count
    count=$(cat "$RALPH_DIR/orchestrator/priority-worker-count")
    assert_equals "0" "$count" "Should not count non-priority workers"
}

test_capacity_sync_ignores_dead_processes() {
    # Create a worker with fixing state but dead PID
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-1234567890"
    mkdir -p "$worker_dir"
    echo '{"current_state": "fixing"}' > "$worker_dir/git-state.json"
    echo "99999" > "$worker_dir/agent.pid"

    echo "5" > "$RALPH_DIR/orchestrator/priority-worker-count"
    _priority_capacity_sync "$RALPH_DIR"

    local count
    count=$(cat "$RALPH_DIR/orchestrator/priority-worker-count")
    assert_equals "0" "$count" "Should not count dead processes"
}

test_capacity_sync_no_crash_without_workers_dir() {
    rmdir "$RALPH_DIR/workers"

    local exit_code=0
    _priority_capacity_sync "$RALPH_DIR" || exit_code=$?
    assert_equals "0" "$exit_code" "Should return 0 when workers dir missing"
}

# =============================================================================
# _verify_task_merged() Tests
# =============================================================================

test_verify_merged_by_kanban_status() {
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
# Kanban

## Complete

- [x] **[TASK-001]** Completed task
  - Description: Done
  - Priority: HIGH
  - Dependencies: none
EOF

    local result
    result=$(_verify_task_merged "$RALPH_DIR" "TASK-001")
    assert_equals "merged" "$result" "Should detect merged from kanban [x]"
}

test_verify_not_merged_pending_approval() {
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
# Kanban

## Pending Approval

- [P] **[TASK-001]** Pending task
  - Description: Test
  - Priority: HIGH
  - Dependencies: none
EOF

    local result exit_code=0
    result=$(_verify_task_merged "$RALPH_DIR" "TASK-001") || exit_code=$?
    assert_equals "1" "$exit_code" "Should return 1 for non-merged task"
    assert_equals "unknown" "$result" "Should output 'unknown' for non-merged task"
}

test_verify_rejects_invalid_task_id() {
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
# Kanban
EOF

    local result exit_code=0
    result=$(_verify_task_merged "$RALPH_DIR" "invalid!!!" "") || exit_code=$?
    assert_equals "1" "$exit_code" "Should return 1 for invalid task ID"
    assert_equals "unknown" "$result" "Should output 'unknown' for invalid task ID"
}

# =============================================================================
# recover_failed_workers() Tests
# =============================================================================

_create_failed_worker() {
    local task_id="$1"
    local reason="$2"
    local recovery_count="${3:-0}"

    local worker_dir="$RALPH_DIR/workers/worker-${task_id}-1234567890"
    mkdir -p "$worker_dir"
    cat > "$worker_dir/git-state.json" << EOF
{
    "current_state": "failed",
    "pr_number": null,
    "merge_attempts": 0,
    "recovery_attempts": $recovery_count,
    "last_error": null,
    "transitions": [{"from": "fixing", "to": "failed", "reason": "$reason"}]
}
EOF
    echo "$worker_dir"
}

test_recover_merge_failure_sets_needs_resolve() {
    local worker_dir
    worker_dir=$(_create_failed_worker "TASK-001" "merge conflict on main")

    cat > "$RALPH_DIR/kanban.md" << 'EOF'
- [P] **[TASK-001]** Test task
  - Description: Test
  - Priority: HIGH
  - Dependencies: none
EOF

    recover_failed_workers "$RALPH_DIR" 2>/dev/null

    local state
    state=$(jq -r '.current_state' "$worker_dir/git-state.json")
    assert_equals "needs_resolve" "$state" "Merge failure should be recovered to needs_resolve"
}

test_recover_unknown_failure_sets_needs_fix() {
    local worker_dir
    worker_dir=$(_create_failed_worker "TASK-001" "UNKNOWN result from agent")

    cat > "$RALPH_DIR/kanban.md" << 'EOF'
- [P] **[TASK-001]** Test task
  - Description: Test
  - Priority: HIGH
  - Dependencies: none
EOF

    recover_failed_workers "$RALPH_DIR" 2>/dev/null

    local state
    state=$(jq -r '.current_state' "$worker_dir/git-state.json")
    assert_equals "needs_fix" "$state" "UNKNOWN failure should be recovered to needs_fix"
}

test_recover_skips_exceeded_max_attempts() {
    local worker_dir
    worker_dir=$(_create_failed_worker "TASK-001" "some error" 5)

    cat > "$RALPH_DIR/kanban.md" << 'EOF'
- [P] **[TASK-001]** Test task
  - Description: Test
  - Priority: HIGH
  - Dependencies: none
EOF

    export WIGGUM_MAX_RECOVERY_ATTEMPTS=2

    local _kanban_failed_called=""
    update_kanban_failed() { _kanban_failed_called="$2"; }

    recover_failed_workers "$RALPH_DIR" 2>/dev/null

    local state
    state=$(jq -r '.current_state' "$worker_dir/git-state.json")
    assert_equals "failed" "$state" "Should stay failed when max attempts exceeded"
    assert_equals "TASK-001" "$_kanban_failed_called" "Should mark kanban as failed"
}

test_recover_skips_completed_tasks() {
    _create_failed_worker "TASK-001" "some error" >/dev/null

    cat > "$RALPH_DIR/kanban.md" << 'EOF'
- [x] **[TASK-001]** Completed task
  - Description: Test
  - Priority: HIGH
  - Dependencies: none
EOF

    # Override get_task_status to return "x" for completed
    get_task_status() { echo "x"; }

    recover_failed_workers "$RALPH_DIR" 2>/dev/null

    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-1234567890"
    local state
    state=$(jq -r '.current_state' "$worker_dir/git-state.json")
    assert_equals "failed" "$state" "Should not recover completed tasks"

    # Restore stub
    get_task_status() { echo "P"; }
}

test_recover_no_crash_without_workers() {
    rmdir "$RALPH_DIR/workers"

    local exit_code=0
    recover_failed_workers "$RALPH_DIR" 2>/dev/null || exit_code=$?
    assert_equals "0" "$exit_code" "Should return 0 when no workers dir"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_capacity_init_creates_file
run_test test_capacity_init_sets_zero
run_test test_capacity_init_preserves_existing
run_test test_capacity_reserve_success_below_limit
run_test test_capacity_reserve_fails_at_limit
run_test test_capacity_reserve_increments_sequentially
run_test test_capacity_release_decrements
run_test test_capacity_release_floors_at_zero
run_test test_capacity_reserve_then_release_roundtrip
run_test test_capacity_sync_resets_to_zero_when_no_workers
run_test test_capacity_sync_ignores_non_priority_workers
run_test test_capacity_sync_ignores_dead_processes
run_test test_capacity_sync_no_crash_without_workers_dir
run_test test_verify_merged_by_kanban_status
run_test test_verify_not_merged_pending_approval
run_test test_verify_rejects_invalid_task_id
run_test test_recover_merge_failure_sets_needs_resolve
run_test test_recover_unknown_failure_sets_needs_fix
run_test test_recover_skips_exceeded_max_attempts
run_test test_recover_skips_completed_tasks
run_test test_recover_no_crash_without_workers

print_test_summary
exit_with_test_result
