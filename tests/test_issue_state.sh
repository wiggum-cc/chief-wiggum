#!/usr/bin/env bash
set -euo pipefail
# Test GitHub issue sync state management (lib/github/issue-state.sh)

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/github/issue-state.sh"

TEST_DIR=""
setup() {
    TEST_DIR=$(mktemp -d)
}
teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# Initialization
# =============================================================================

test_state_init_creates_file() {
    github_sync_state_init "$TEST_DIR"
    assert_file_exists "$TEST_DIR/github-sync-state.json" "State file should be created"
}

test_state_init_valid_json() {
    github_sync_state_init "$TEST_DIR"
    local version
    version=$(jq -r '.version' "$TEST_DIR/github-sync-state.json")
    assert_equals "2.0" "$version" "Should have version 2.0"
}

test_state_init_idempotent() {
    github_sync_state_init "$TEST_DIR"
    # Add a task
    github_sync_state_set_task "$TEST_DIR" "GH-42" '{"issue_number":42}'
    # Re-init should NOT overwrite
    github_sync_state_init "$TEST_DIR"
    local task
    task=$(github_sync_state_get_task "$TEST_DIR" "GH-42")
    assert_not_equals "null" "$task" "Re-init should not overwrite existing state"
}

# =============================================================================
# Task CRUD
# =============================================================================

test_state_set_and_get_task() {
    github_sync_state_init "$TEST_DIR"

    local entry='{"issue_number":42,"last_synced_status":" ","last_remote_state":"open"}'
    github_sync_state_set_task "$TEST_DIR" "GH-42" "$entry"

    local result
    result=$(github_sync_state_get_task "$TEST_DIR" "GH-42")
    local issue_number
    issue_number=$(echo "$result" | jq -r '.issue_number')
    assert_equals "42" "$issue_number" "Should retrieve stored task"
}

test_state_get_nonexistent_task() {
    github_sync_state_init "$TEST_DIR"
    local result
    result=$(github_sync_state_get_task "$TEST_DIR" "GH-999")
    assert_equals "null" "$result" "Nonexistent task should return null"
}

test_state_remove_task() {
    github_sync_state_init "$TEST_DIR"

    local entry='{"issue_number":42}'
    github_sync_state_set_task "$TEST_DIR" "GH-42" "$entry"
    github_sync_state_remove_task "$TEST_DIR" "GH-42"

    local result
    result=$(github_sync_state_get_task "$TEST_DIR" "GH-42")
    assert_equals "null" "$result" "Removed task should return null"
}

test_state_list_tasks() {
    github_sync_state_init "$TEST_DIR"

    github_sync_state_set_task "$TEST_DIR" "GH-10" '{"issue_number":10}'
    github_sync_state_set_task "$TEST_DIR" "GH-20" '{"issue_number":20}'
    github_sync_state_set_task "$TEST_DIR" "GH-30" '{"issue_number":30}'

    local result
    result=$(github_sync_state_list_tasks "$TEST_DIR")
    local count
    count=$(echo "$result" | wc -l)

    assert_equals "3" "$count" "Should list 3 tracked tasks"
    assert_output_contains "$result" "GH-10" "Should list task GH-10"
    assert_output_contains "$result" "GH-20" "Should list task GH-20"
    assert_output_contains "$result" "GH-30" "Should list task GH-30"
}

test_state_find_task_by_issue() {
    github_sync_state_init "$TEST_DIR"

    github_sync_state_set_task "$TEST_DIR" "GH-42" '{"issue_number":42}'
    github_sync_state_set_task "$TEST_DIR" "FEAT-7" '{"issue_number":7}'

    local result
    result=$(github_sync_state_find_task_by_issue "$TEST_DIR" 42)
    assert_equals "GH-42" "$result" "Should find GH-42 by issue number 42"

    result=$(github_sync_state_find_task_by_issue "$TEST_DIR" 7)
    assert_equals "FEAT-7" "$result" "Should find FEAT-7 by issue number 7"

    result=$(github_sync_state_find_task_by_issue "$TEST_DIR" 999)
    assert_equals "" "$result" "Should return empty for unknown issue number"
}

# =============================================================================
# Timestamp Updates
# =============================================================================

test_state_set_down_sync_time() {
    github_sync_state_init "$TEST_DIR"
    github_sync_state_set_down_sync_time "$TEST_DIR" 1706000000

    local result
    result=$(jq -r '.last_down_sync_at' "$TEST_DIR/github-sync-state.json")
    assert_equals "1706000000" "$result" "Should update down sync timestamp"
}

test_state_set_up_sync_time() {
    github_sync_state_init "$TEST_DIR"
    github_sync_state_set_up_sync_time "$TEST_DIR" 1706000100

    local result
    result=$(jq -r '.last_up_sync_at' "$TEST_DIR/github-sync-state.json")
    assert_equals "1706000100" "$result" "Should update up sync timestamp"
}

# =============================================================================
# Entry Creation
# =============================================================================

test_state_create_entry() {
    local entry
    entry=$(github_sync_state_create_entry 42 "2025-01-23T12:00:00Z" " " "open" "sha256:abc123")

    local issue_number status state pr_linked
    issue_number=$(echo "$entry" | jq -r '.issue_number')
    status=$(echo "$entry" | jq -r '.last_synced_status')
    state=$(echo "$entry" | jq -r '.last_remote_state')
    pr_linked=$(echo "$entry" | jq -r '.pr_linked')

    assert_equals "42" "$issue_number" "Entry should have issue_number"
    assert_equals " " "$status" "Entry should have pending status"
    assert_equals "open" "$state" "Entry should have open state"
    assert_equals "false" "$pr_linked" "Entry should have pr_linked=false"
}

# =============================================================================
# Content Hashing
# =============================================================================

test_hash_content() {
    local hash1 hash2
    hash1=$(github_sync_hash_content "hello world")
    hash2=$(github_sync_hash_content "hello world")

    assert_equals "$hash1" "$hash2" "Same content should produce same hash"
    assert_output_contains "$hash1" "sha256:" "Hash should have sha256: prefix"
}

test_hash_different_content() {
    local hash1 hash2
    hash1=$(github_sync_hash_content "hello world")
    hash2=$(github_sync_hash_content "different content")

    assert_not_equals "$hash1" "$hash2" "Different content should produce different hash"
}

# =============================================================================
# Atomic Save
# =============================================================================

test_state_save_atomic() {
    github_sync_state_init "$TEST_DIR"

    # Save valid JSON
    local state='{"version":"2.0","last_down_sync_at":100,"last_up_sync_at":200,"issues":{}}'
    github_sync_state_save "$TEST_DIR" "$state"

    local result
    result=$(jq -r '.last_down_sync_at' "$TEST_DIR/github-sync-state.json")
    assert_equals "100" "$result" "Should save valid JSON atomically"
}

test_state_save_invalid_json_fails() {
    github_sync_state_init "$TEST_DIR"

    # Attempt to save invalid JSON should fail
    local exit_code=0
    github_sync_state_save "$TEST_DIR" "not valid json" || exit_code=$?

    assert_equals "1" "$exit_code" "Should fail on invalid JSON"

    # Original file should still be valid
    local version
    version=$(jq -r '.version' "$TEST_DIR/github-sync-state.json")
    assert_equals "2.0" "$version" "Original file should remain valid after failed save"
}

# =============================================================================
# Load from Missing File
# =============================================================================

test_state_load_missing_file() {
    local result
    result=$(github_sync_state_load "$TEST_DIR/nonexistent")

    local version
    version=$(echo "$result" | jq -r '.version')
    assert_equals "2.0" "$version" "Missing file should return default state"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_state_init_creates_file
run_test test_state_init_valid_json
run_test test_state_init_idempotent
run_test test_state_set_and_get_task
run_test test_state_get_nonexistent_task
run_test test_state_remove_task
run_test test_state_list_tasks
run_test test_state_find_task_by_issue
run_test test_state_set_down_sync_time
run_test test_state_set_up_sync_time
run_test test_state_create_entry
run_test test_hash_content
run_test test_hash_different_content
run_test test_state_save_atomic
run_test test_state_save_invalid_json_fails
run_test test_state_load_missing_file

print_test_summary
exit_with_test_result
