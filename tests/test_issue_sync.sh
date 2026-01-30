#!/usr/bin/env bash
set -euo pipefail
# Test GitHub issue sync logic (lib/github/issue-sync.sh)
#
# These tests mock the `gh` CLI and `timeout` to test sync behavior
# without real GitHub API calls.

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/github/issue-config.sh"
source "$WIGGUM_HOME/lib/github/issue-state.sh"
source "$WIGGUM_HOME/lib/github/issue-parser.sh"
source "$WIGGUM_HOME/lib/github/issue-writer.sh"

# Suppress log output in tests
LOG_LEVEL=ERROR
export LOG_LEVEL

TEST_DIR=""
MOCK_BIN=""

setup() {
    TEST_DIR=$(mktemp -d)
    MOCK_BIN="$TEST_DIR/bin"
    mkdir -p "$MOCK_BIN" "$TEST_DIR/.ralph"

    # Set config globals for tests
    GITHUB_SYNC_ENABLED="true"
    GITHUB_SYNC_ALLOWED_USER_IDS="12345"
    GITHUB_SYNC_ALLOWED_USERNAMES="testuser"
    GITHUB_SYNC_LABEL_FILTER="wiggum"
    GITHUB_SYNC_DEFAULT_PRIORITY="MEDIUM"
    # shellcheck disable=SC2089 # JSON strings, not bash arrays
    GITHUB_SYNC_PRIORITY_LABELS='{"priority:critical":"CRITICAL","priority:high":"HIGH","priority:medium":"MEDIUM","priority:low":"LOW"}'
    # shellcheck disable=SC2089 # JSON strings, not bash arrays
    GITHUB_SYNC_STATUS_LABELS='{"wiggum:in-progress":"=","wiggum:pending-approval":"P","wiggum:completed":"x","wiggum:failed":"*","wiggum:not-planned":"N"}'
    GITHUB_SYNC_CLOSE_ON="x"
    export GITHUB_SYNC_ENABLED GITHUB_SYNC_ALLOWED_USER_IDS GITHUB_SYNC_ALLOWED_USERNAMES
    export GITHUB_SYNC_LABEL_FILTER GITHUB_SYNC_DEFAULT_PRIORITY
    # shellcheck disable=SC2090 # JSON strings passed to jq, not bash expansions
    export GITHUB_SYNC_PRIORITY_LABELS GITHUB_SYNC_STATUS_LABELS GITHUB_SYNC_CLOSE_ON

    # Create a basic kanban file
    cat > "$TEST_DIR/.ralph/kanban.md" << 'EOF'
# Kanban Board

## TASKS

- [ ] **[EXIST-1]** Existing pending task
  - Description: Already in kanban
  - Priority: LOW
  - Dependencies: none
- [=] **[EXIST-2]** In-progress task
  - Description: Currently being worked on
  - Priority: HIGH
  - Dependencies: none
EOF
}

teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# Config Tests
# =============================================================================

test_config_is_enabled() {
    assert_success "Sync should be enabled" github_sync_is_enabled
}

test_config_is_disabled() {
    GITHUB_SYNC_ENABLED="false"
    assert_failure "Sync should be disabled" github_sync_is_enabled
    GITHUB_SYNC_ENABLED="true"
}

test_config_get_status_label() {
    local label
    label=$(github_sync_get_status_label "=")
    assert_equals "wiggum:in-progress" "$label" "Should map = to wiggum:in-progress"
}

test_config_get_status_label_completed() {
    local label
    label=$(github_sync_get_status_label "x")
    assert_equals "wiggum:completed" "$label" "Should map x to wiggum:completed"
}

test_config_get_status_char() {
    local char
    char=$(github_sync_get_status_char "wiggum:failed")
    assert_equals "*" "$char" "Should map wiggum:failed to *"
}

test_config_should_close() {
    assert_success "x should close" github_sync_should_close "x"
    assert_failure "N should not close" github_sync_should_close "N"
    assert_failure "= should not close" github_sync_should_close "="
    assert_failure "* should not close" github_sync_should_close "*"
}

# =============================================================================
# Author Validation
# =============================================================================

test_author_allowed_by_id() {
    assert_success "User 12345 should be allowed" \
        github_sync_is_author_allowed "12345" "anyname"
}

test_author_allowed_by_username() {
    assert_success "testuser should be allowed" \
        github_sync_is_author_allowed "" "testuser"
}

test_author_allowed_case_insensitive() {
    assert_success "TestUser should be allowed (case insensitive)" \
        github_sync_is_author_allowed "" "TestUser"
}

test_author_not_allowed() {
    assert_failure "Unknown user should not be allowed" \
        github_sync_is_author_allowed "99999" "unknownuser"
}

# =============================================================================
# Priority from Labels
# =============================================================================

test_priority_from_labels() {
    local result
    result=$(github_sync_get_priority_from_labels '[{"name":"wiggum"},{"name":"priority:high"}]')
    assert_equals "HIGH" "$result" "Should extract HIGH from labels"
}

test_priority_from_labels_multiple() {
    local result
    result=$(github_sync_get_priority_from_labels '[{"name":"priority:low"},{"name":"priority:critical"}]')
    assert_equals "CRITICAL" "$result" "Should pick highest priority"
}

test_priority_from_labels_none() {
    local result
    result=$(github_sync_get_priority_from_labels '[{"name":"wiggum"},{"name":"bug"}]')
    assert_equals "" "$result" "Should return empty with no priority labels"
}

# =============================================================================
# Kanban Task Management
# =============================================================================

test_add_kanban_task() {
    local kanban="$TEST_DIR/.ralph/kanban.md"
    add_kanban_task "$kanban" "GH-42" "Add dark mode" \
        "Support dark/light toggling" "HIGH" "GH-30" ""

    assert_file_contains "$kanban" "**[GH-42]**" "Should add task ID"
    assert_file_contains "$kanban" "Add dark mode" "Should add brief"
    assert_file_contains "$kanban" "Priority: HIGH" "Should add priority"
    assert_file_contains "$kanban" "Dependencies: GH-30" "Should add dependencies"
}

test_add_kanban_task_duplicate() {
    local kanban="$TEST_DIR/.ralph/kanban.md"

    local exit_code=0
    add_kanban_task "$kanban" "EXIST-1" "Duplicate" "Desc" "MEDIUM" "none" "" || exit_code=$?

    assert_equals "1" "$exit_code" "Should fail on duplicate task"
}

test_add_kanban_task_with_extra_fields() {
    local kanban="$TEST_DIR/.ralph/kanban.md"
    local extras
    extras=$(printf 'Complexity: HIGH\nScope: Build feature X')

    add_kanban_task "$kanban" "GH-99" "New feature" \
        "Build it" "MEDIUM" "none" "$extras"

    assert_file_contains "$kanban" "Complexity: HIGH" "Should add complexity"
    assert_file_contains "$kanban" "Scope: Build feature X" "Should add scope"
}

test_update_kanban_task_fields() {
    local kanban="$TEST_DIR/.ralph/kanban.md"

    update_kanban_task_fields "$kanban" "EXIST-1" \
        "Updated description" "HIGH" "EXIST-2"

    assert_file_contains "$kanban" "Description: Updated description" "Should update description"
    assert_file_contains "$kanban" "Priority: HIGH" "Should update priority"
    assert_file_contains "$kanban" "Dependencies: EXIST-2" "Should update dependencies"
}

test_update_kanban_task_fields_not_found() {
    local kanban="$TEST_DIR/.ralph/kanban.md"

    local exit_code=0
    update_kanban_task_fields "$kanban" "NONEXIST-1" "Desc" "HIGH" "none" || exit_code=$?

    assert_equals "1" "$exit_code" "Should fail for non-existent task"
}

# =============================================================================
# State Management Integration
# =============================================================================

test_state_full_lifecycle() {
    local ralph_dir="$TEST_DIR/.ralph"

    # Init
    github_sync_state_init "$ralph_dir"
    assert_file_exists "$ralph_dir/github-sync-state.json" "State file should exist"

    # Add issue
    local entry
    entry=$(github_sync_state_create_entry "GH-42" "2025-01-23T12:00:00Z" " " "open" "sha256:abc")
    github_sync_state_set_issue "$ralph_dir" "42" "$entry"

    # Verify
    local retrieved
    retrieved=$(github_sync_state_get_issue "$ralph_dir" "42")
    local task_id
    task_id=$(echo "$retrieved" | jq -r '.task_id')
    assert_equals "GH-42" "$task_id" "Should retrieve stored issue"

    # Update timestamps
    github_sync_state_set_down_sync_time "$ralph_dir" 1706000000
    github_sync_state_set_up_sync_time "$ralph_dir" 1706000100

    # Verify timestamps
    local down_ts up_ts
    down_ts=$(jq -r '.last_down_sync_at' "$ralph_dir/github-sync-state.json")
    up_ts=$(jq -r '.last_up_sync_at' "$ralph_dir/github-sync-state.json")
    assert_equals "1706000000" "$down_ts" "Should have down sync timestamp"
    assert_equals "1706000100" "$up_ts" "Should have up sync timestamp"

    # List issues
    local issues
    issues=$(github_sync_state_list_issues "$ralph_dir")
    assert_output_contains "$issues" "42" "Should list issue 42"

    # Remove
    github_sync_state_remove_issue "$ralph_dir" "42"
    local after
    after=$(github_sync_state_get_issue "$ralph_dir" "42")
    assert_equals "null" "$after" "Should be null after removal"
}

# =============================================================================
# Issue Writer Status Mapping
# =============================================================================

test_writer_status_name_mapping() {
    # Test the internal _kanban_status_name function via its use in update_status
    # We can't call _kanban_status_name directly since it's in issue-writer.sh
    # but we can verify the status labels work correctly

    local label
    label=$(github_sync_get_status_label " ")
    assert_equals "" "$label" "Pending should have no label"

    label=$(github_sync_get_status_label "=")
    assert_equals "wiggum:in-progress" "$label" "In-progress label"

    label=$(github_sync_get_status_label "P")
    assert_equals "wiggum:pending-approval" "$label" "Pending approval label"

    label=$(github_sync_get_status_label "x")
    assert_equals "wiggum:completed" "$label" "Completed label"

    label=$(github_sync_get_status_label "*")
    assert_equals "wiggum:failed" "$label" "Failed label"

    label=$(github_sync_get_status_label "N")
    assert_equals "wiggum:not-planned" "$label" "Not-planned label"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_config_is_enabled
run_test test_config_is_disabled
run_test test_config_get_status_label
run_test test_config_get_status_label_completed
run_test test_config_get_status_char
run_test test_config_should_close
run_test test_author_allowed_by_id
run_test test_author_allowed_by_username
run_test test_author_allowed_case_insensitive
run_test test_author_not_allowed
run_test test_priority_from_labels
run_test test_priority_from_labels_multiple
run_test test_priority_from_labels_none
run_test test_add_kanban_task
run_test test_add_kanban_task_duplicate
run_test test_add_kanban_task_with_extra_fields
run_test test_update_kanban_task_fields
run_test test_update_kanban_task_fields_not_found
run_test test_state_full_lifecycle
run_test test_writer_status_name_mapping

print_test_summary
exit_with_test_result
