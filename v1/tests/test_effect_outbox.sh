#!/usr/bin/env bash
# Test suite for effect-outbox.sh - crash-safe effect execution
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
source "$SCRIPT_DIR/test-framework.sh"

export WIGGUM_HOME="$SCRIPT_DIR/.."
source "$WIGGUM_HOME/lib/core/effect-outbox.sh"

setup() {
    TEST_WORKER_DIR=$(mktemp -d)
}

teardown() {
    rm -rf "$TEST_WORKER_DIR"
}

# =============================================================================
# Tests
# =============================================================================

test_outbox_record_pending() {
    setup

    local batch_id
    batch_id=$(outbox_record_pending "$TEST_WORKER_DIR" "sync_github,cleanup_worktree" '{"task_id":"TEST-001"}')

    assert_file_exists "$TEST_WORKER_DIR/pending-effects.json"
    [[ "$batch_id" == batch-* ]] || fail "Batch ID should start with 'batch-'"

    local pending_count
    pending_count=$(jq '.pending | length' "$TEST_WORKER_DIR/pending-effects.json")
    assert_equals "2" "$pending_count"

    local first_effect
    first_effect=$(jq -r '.pending[0].effect' "$TEST_WORKER_DIR/pending-effects.json")
    assert_equals "sync_github" "$first_effect"

    teardown
}

test_outbox_mark_completed() {
    setup

    local batch_id
    batch_id=$(outbox_record_pending "$TEST_WORKER_DIR" "effect1,effect2" '{}')

    outbox_mark_completed "$TEST_WORKER_DIR" "${batch_id}-effect1"

    local pending_count
    pending_count=$(jq '.pending | length' "$TEST_WORKER_DIR/pending-effects.json")
    assert_equals "1" "$pending_count"

    local completed_count
    completed_count=$(jq '.completed | length' "$TEST_WORKER_DIR/pending-effects.json")
    assert_equals "1" "$completed_count"

    teardown
}

test_outbox_mark_batch_completed() {
    setup

    local batch_id
    batch_id=$(outbox_record_pending "$TEST_WORKER_DIR" "effect1,effect2,effect3" '{}')

    outbox_mark_batch_completed "$TEST_WORKER_DIR" "$batch_id"

    local pending_count
    pending_count=$(jq '.pending | length' "$TEST_WORKER_DIR/pending-effects.json")
    assert_equals "0" "$pending_count"

    local completed_count
    completed_count=$(jq '.completed | length' "$TEST_WORKER_DIR/pending-effects.json")
    assert_equals "3" "$completed_count"

    teardown
}

test_outbox_has_pending() {
    setup

    # Initially no pending effects
    if outbox_has_pending "$TEST_WORKER_DIR"; then
        fail "Should not have pending effects initially"
    fi

    # Add pending effects
    outbox_record_pending "$TEST_WORKER_DIR" "effect1" '{}' > /dev/null

    if ! outbox_has_pending "$TEST_WORKER_DIR"; then
        fail "Should have pending effects after recording"
    fi

    teardown
}

test_outbox_get_pending() {
    setup

    outbox_record_pending "$TEST_WORKER_DIR" "effect1,effect2" '{"key":"value"}' > /dev/null

    local pending
    pending=$(outbox_get_pending "$TEST_WORKER_DIR")

    local count
    count=$(echo "$pending" | jq 'length')
    assert_equals "2" "$count"

    local args_key
    args_key=$(echo "$pending" | jq -r '.[0].args.key')
    assert_equals "value" "$args_key"

    teardown
}

test_outbox_cleanup_completed() {
    setup

    # Create outbox with many completed entries
    echo '{"pending":[],"completed":["a","b","c","d","e"]}' > "$TEST_WORKER_DIR/pending-effects.json"

    outbox_cleanup_completed "$TEST_WORKER_DIR"

    # Should still have all 5 (under the 100 limit)
    local count
    count=$(jq '.completed | length' "$TEST_WORKER_DIR/pending-effects.json")
    assert_equals "5" "$count"

    teardown
}

test_outbox_clear() {
    setup

    outbox_record_pending "$TEST_WORKER_DIR" "effect1" '{}' > /dev/null
    assert_file_exists "$TEST_WORKER_DIR/pending-effects.json"

    outbox_clear "$TEST_WORKER_DIR"

    if [ -f "$TEST_WORKER_DIR/pending-effects.json" ]; then
        fail "Outbox file should be deleted after clear"
    fi

    teardown
}

test_outbox_preserves_context() {
    setup

    local context='{"task_id":"FEAT-123","ralph_dir":"/tmp/ralph","kanban":"x"}'
    outbox_record_pending "$TEST_WORKER_DIR" "sync_github" "$context" > /dev/null

    local stored_task_id
    stored_task_id=$(jq -r '.pending[0].args.task_id' "$TEST_WORKER_DIR/pending-effects.json")
    assert_equals "FEAT-123" "$stored_task_id"

    local stored_kanban
    stored_kanban=$(jq -r '.pending[0].args.kanban' "$TEST_WORKER_DIR/pending-effects.json")
    assert_equals "x" "$stored_kanban"

    teardown
}

# =============================================================================
# Run tests
# =============================================================================

run_test "test_outbox_record_pending"
run_test "test_outbox_mark_completed"
run_test "test_outbox_mark_batch_completed"
run_test "test_outbox_has_pending"
run_test "test_outbox_get_pending"
run_test "test_outbox_cleanup_completed"
run_test "test_outbox_clear"
run_test "test_outbox_preserves_context"

print_test_summary
