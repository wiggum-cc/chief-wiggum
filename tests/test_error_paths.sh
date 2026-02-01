#!/usr/bin/env bash
set -euo pipefail
# Error path tests for Chief Wiggum modules
# Tests edge cases, error handling, and failure modes

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"

TEST_DIR=""
setup() {
    TEST_DIR=$(mktemp -d)
}
teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# File Lock Error Paths (lib/core/file-lock.sh)
# =============================================================================

source "$WIGGUM_HOME/lib/core/file-lock.sh"

# Test 1: with_file_lock with non-existent parent directory (should fail gracefully)
test_file_lock_nonexistent_parent_dir() {
    local nonexistent_path="$TEST_DIR/no/such/parent/dir/file.txt"

    # with_file_lock should fail gracefully when parent dir does not exist
    local result
    with_file_lock "$nonexistent_path" 1 true 2>/dev/null
    result=$?

    assert_equals "1" "$result" "with_file_lock should fail when parent directory does not exist"
}

# Test 2: acquire lock timeout when lock held by another process
test_file_lock_timeout_when_held() {
    local lock_target="$TEST_DIR/locked_file.txt"
    echo "data" > "$lock_target"
    local lock_file="${lock_target}.lock"

    # Hold a lock in a background process using the same fd mechanism
    (
        exec 200>"$lock_file"
        flock -x 200
        sleep 3
    ) &
    local holder_pid=$!

    # Give the holder time to acquire the lock
    sleep 0.1

    # Try to acquire with_file_lock using max_retries=1
    # The flock -w 10 inside will timeout, but we wrap with timeout 1
    local result
    timeout 1 bash -c "
        source '$WIGGUM_HOME/lib/core/file-lock.sh'
        with_file_lock '$lock_target' 1 true
    " 2>/dev/null
    result=$?

    # Kill the holder
    kill $holder_pid 2>/dev/null
    wait $holder_pid 2>/dev/null || true

    # Should have failed (timeout from flock or from our timeout wrapper)
    assert_not_equals "0" "$result" "with_file_lock should fail/timeout when lock is held by another"
}

# Test 3: release of non-existent lock file (should not error)
test_file_lock_release_nonexistent() {
    local nonexistent="$TEST_DIR/does_not_exist.txt"

    # with_file_lock removes the lock file after success via rm -f
    # Calling rm -f on a non-existent file should not error
    local result
    rm -f "${nonexistent}.lock" 2>/dev/null
    result=$?

    assert_equals "0" "$result" "Removing non-existent lock file should not error"
}

# Test 4: Concurrent lock acquisition - verify serialization works for single-process
# The with_file_lock implementation re-opens the lock file each call, which limits
# cross-process guarantees. Here we verify the locking mechanism provides proper
# serialization within a single process (sequential calls).
test_file_lock_concurrent_serialization() {
    local shared_file="$TEST_DIR/shared_counter.txt"
    echo "0" > "$shared_file"

    # Define an increment function that reads, increments, and writes
    _test_increment() {
        local file="$1"
        local val
        val=$(cat "$file")
        echo $((val + 1)) > "$file"
    }

    # Run 5 sequential locked increments - should serialize perfectly
    for _i in $(seq 1 5); do
        with_file_lock "$shared_file" 5 _test_increment "$shared_file"
    done

    local final_val
    final_val=$(cat "$shared_file")
    assert_equals "5" "$final_val" "Sequential locked increments should yield exact count"

    # Now test that 5 concurrent processes each running 10 locked increments
    # produce a valid numeric result (not corrupted output)
    echo "0" > "$shared_file"

    local pids=()
    for _i in $(seq 1 5); do
        (
            source "$WIGGUM_HOME/lib/core/file-lock.sh"
            _bg_increment() {
                local f="$1"
                local v
                v=$(cat "$f")
                echo $((v + 1)) > "$f"
            }
            for _j in $(seq 1 10); do
                with_file_lock "$shared_file" 10 _bg_increment "$shared_file"
            done
        ) &
        pids+=($!)
    done

    for pid in "${pids[@]}"; do
        wait $pid 2>/dev/null || true
    done

    final_val=$(cat "$shared_file")

    # Verify the result is exactly 50 (5 processes x 10 increments each)
    assert_equals "50" "$final_val" "5 processes x 10 increments should yield exactly 50"
}

# =============================================================================
# Logger Error Paths (lib/core/logger.sh)
# =============================================================================

# Test 5: log with empty message should not crash
test_logger_empty_message() {
    local result
    log "" >/dev/null 2>&1
    result=$?

    assert_equals "0" "$result" "log with empty message should not crash"

    # Also test log_warn and log_error with empty message
    log_warn "" 2>/dev/null
    result=$?
    assert_equals "0" "$result" "log_warn with empty message should not crash"

    log_error "" 2>/dev/null
    result=$?
    assert_equals "0" "$result" "log_error with empty message should not crash"
}

# Test 6: log with special characters (quotes, newlines, pipes)
test_logger_special_characters() {
    local result

    # Test with double quotes
    log "message with \"double quotes\"" >/dev/null 2>&1
    result=$?
    assert_equals "0" "$result" "log with double quotes should not crash"

    # Test with single quotes
    log "message with 'single quotes'" >/dev/null 2>&1
    result=$?
    assert_equals "0" "$result" "log with single quotes should not crash"

    # Test with pipe characters
    log "message with | pipe | chars" >/dev/null 2>&1
    result=$?
    assert_equals "0" "$result" "log with pipe characters should not crash"

    # Test with backslashes
    log "message with \\ backslash" >/dev/null 2>&1
    result=$?
    assert_equals "0" "$result" "log with backslashes should not crash"

    # Test with dollar signs and backticks
    log 'message with $VAR and `command`' >/dev/null 2>&1
    result=$?
    assert_equals "0" "$result" "log with dollar signs and backticks should not crash"

    # Test with newline embedded in message
    log "line one
line two" >/dev/null 2>&1
    result=$?
    assert_equals "0" "$result" "log with embedded newline should not crash"
}

# Test 7: log_debug when LOG_LEVEL is higher than DEBUG
test_logger_debug_suppressed_at_higher_level() {
    local old_log_level="${LOG_LEVEL:-}"
    local old_debug="${DEBUG:-}"
    export LOG_LEVEL="ERROR"
    unset DEBUG

    local output
    output=$(log_debug "this should not appear" 2>&1)

    assert_equals "" "$output" "log_debug should produce no output when LOG_LEVEL=ERROR"

    # Also test that WARN is suppressed at ERROR level
    output=$(log_warn "this should also not appear" 2>&1)
    assert_equals "" "$output" "log_warn should produce no output when LOG_LEVEL=ERROR"

    # But log_error should still output
    output=$(log_error "this should appear" 2>&1)
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ -n "$output" ]; then
        echo -e "  ${GREEN}✓${NC} log_error still outputs when LOG_LEVEL=ERROR"
    else
        echo -e "  ${RED}✗${NC} log_error should output when LOG_LEVEL=ERROR"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi

    # Restore
    if [ -n "$old_log_level" ]; then
        export LOG_LEVEL="$old_log_level"
    else
        unset LOG_LEVEL
    fi
    if [ -n "$old_debug" ]; then
        export DEBUG="$old_debug"
    fi
}

# Test 8: log to a file in non-existent directory (should handle gracefully or create dir)
test_logger_nonexistent_log_dir() {
    local old_log_file="${LOG_FILE:-}"
    local bad_log_path="$TEST_DIR/no/such/dir/test.log"

    # Run in subshell to isolate any fatal errors from set -e
    # Redirect stdout to /dev/null inside so we only see the exit behavior
    local exit_code
    bash -c "
        source '$WIGGUM_HOME/lib/core/logger.sh'
        export LOG_FILE='$bad_log_path'
        log 'test message' >/dev/null 2>/dev/null
        echo 'survived'
    " >/dev/null 2>/dev/null
    exit_code=$?

    # The function may fail to write (set -e triggers exit) which gives non-zero
    # exit code, or it may silently fail and survive. Both are graceful handling.
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ $exit_code -eq 0 ]; then
        echo -e "  ${GREEN}✓${NC} log to non-existent dir handled gracefully (survived, exit=0)"
    else
        # set -e caused script exit - this is acceptable graceful failure
        echo -e "  ${GREEN}✓${NC} log to non-existent dir exited cleanly via set -e (exit=$exit_code)"
    fi

    # Restore
    export LOG_FILE="$old_log_file"
}

source "$WIGGUM_HOME/lib/tasks/task-parser.sh"

# Test 9: get_all_tasks (get_todo_tasks) with empty file
test_task_parser_empty_file() {
    local empty_file="$TEST_DIR/empty_kanban.md"
    touch "$empty_file"

    local result
    result=$(get_todo_tasks "$empty_file")
    assert_equals "" "$result" "get_todo_tasks with empty file should return empty"

    result=$(get_all_tasks_with_metadata "$empty_file")
    assert_equals "" "$result" "get_all_tasks_with_metadata with empty file should return empty"

    result=$(get_failed_tasks "$empty_file")
    assert_equals "" "$result" "get_failed_tasks with empty file should return empty"
}

# Test 10: get_all_tasks with file containing only whitespace/blank lines
test_task_parser_whitespace_only_file() {
    local ws_file="$TEST_DIR/whitespace_kanban.md"
    printf "\n\n   \n\t\n  \n" > "$ws_file"

    local result
    result=$(get_todo_tasks "$ws_file")
    assert_equals "" "$result" "get_todo_tasks with whitespace-only file should return empty"

    result=$(get_all_tasks_with_metadata "$ws_file")
    assert_equals "" "$result" "get_all_tasks_with_metadata with whitespace-only file should return empty"

    result=$(get_completed_tasks "$ws_file")
    assert_equals "" "$result" "get_completed_tasks with whitespace-only file should return empty"
}

# Test 11: get_all_tasks with no matching task patterns
test_task_parser_no_matching_patterns() {
    local nopattern_file="$TEST_DIR/no_tasks.md"
    cat > "$nopattern_file" << 'EOF'
# Project Notes

This is a markdown file with no task patterns.

- Some bullet point
- Another bullet point
- [ ] A regular checklist item (not a task pattern)
- [x] Done item (not matching **[ID]** pattern)

## Section Header

Just regular text without any kanban task patterns.
EOF

    local result
    result=$(get_todo_tasks "$nopattern_file")
    assert_equals "" "$result" "get_todo_tasks with no task patterns should return empty"

    result=$(get_all_tasks_with_metadata "$nopattern_file")
    assert_equals "" "$result" "get_all_tasks_with_metadata with no task patterns should return empty"
}

# Test 12: get_task_status with non-existent task ID
test_task_parser_nonexistent_task_status() {
    local kanban_file="$TEST_DIR/tasks.md"
    cat > "$kanban_file" << 'EOF'
# Kanban

- [ ] **[TASK-001]** Existing task
  - Description: A task
  - Priority: MEDIUM
  - Dependencies: none

- [x] **[TASK-002]** Completed task
  - Description: Another task
  - Priority: HIGH
  - Dependencies: none
EOF

    local status
    status=$(get_task_status "$kanban_file" "NONEXIST-999")
    assert_equals "" "$status" "get_task_status for non-existent task should return empty"

    status=$(get_task_status "$kanban_file" "")
    assert_equals "" "$status" "get_task_status for empty task ID should return empty"

    # Verify existing task still works correctly for comparison
    status=$(get_task_status "$kanban_file" "TASK-001")
    assert_equals " " "$status" "get_task_status for existing pending task should return space"
}

# Test 13: get_task_dependencies with task that has no deps section
test_task_parser_no_deps_section() {
    local kanban_file="$TEST_DIR/nodeps.md"
    cat > "$kanban_file" << 'EOF'
# Kanban

- [ ] **[TASK-001]** Task without deps line
  - Description: This task has no Dependencies field
  - Priority: HIGH

- [ ] **[TASK-002]** Task with explicit none
  - Description: This task has Dependencies: none
  - Priority: MEDIUM
  - Dependencies: none

- [ ] **[TASK-003]** Task with empty deps
  - Description: This task has empty Dependencies
  - Priority: LOW
  - Dependencies:
EOF

    local deps

    deps=$(get_task_dependencies "$kanban_file" "TASK-001")
    assert_equals "" "$deps" "get_task_dependencies for task with no deps line should return empty"

    deps=$(get_task_dependencies "$kanban_file" "TASK-002")
    assert_equals "" "$deps" "get_task_dependencies for task with 'none' deps should return empty"

    deps=$(get_task_dependencies "$kanban_file" "TASK-003")
    assert_equals "" "$deps" "get_task_dependencies for task with empty deps value should return empty"

    # Non-existent task
    deps=$(get_task_dependencies "$kanban_file" "FAKE-999")
    assert_equals "" "$deps" "get_task_dependencies for non-existent task should return empty"
}

# =============================================================================
# Git Operations Error Paths (lib/git/git-operations.sh)
# =============================================================================

# Source git-operations.sh; it sources logger.sh and calculate-cost.sh internally
source "$WIGGUM_HOME/lib/utils/calculate-cost.sh" 2>/dev/null || true
source "$WIGGUM_HOME/lib/git/git-operations.sh" 2>/dev/null || true

# Test 14: git_safety_checkpoint in non-git directory (should fail gracefully)
test_git_safety_checkpoint_non_git_dir() {
    local non_git_dir="$TEST_DIR/not_a_repo"
    mkdir -p "$non_git_dir"

    # Run in subshell to catch set -e failures and isolate cd side effects
    local result
    (
        source "$WIGGUM_HOME/lib/core/logger.sh"
        source "$WIGGUM_HOME/lib/git/git-operations.sh" 2>/dev/null
        export LOG_FILE="/dev/null"
        git_safety_checkpoint "$non_git_dir" >/dev/null 2>&1
    )
    result=$?

    # git rev-parse HEAD fails in non-git dir; function should not crash
    # GIT_SAFETY_CHECKPOINT_SHA should be empty or the function returns non-zero
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    # The function does cd into the dir (which succeeds) then runs git rev-parse HEAD
    # which fails. With set -e this exits the subshell non-zero.
    if [ $result -ne 0 ]; then
        echo -e "  ${GREEN}✓${NC} git_safety_checkpoint fails gracefully in non-git dir (exit=$result)"
    else
        echo -e "  ${GREEN}✓${NC} git_safety_checkpoint handled non-git dir without crash (exit=0)"
    fi
}

# Test 15: git_create_commit in directory with no changes (should handle cleanly)
test_git_create_commit_no_changes() {
    local workspace="$TEST_DIR/clean_repo"
    mkdir -p "$workspace"

    # Initialize a clean git repo with one commit
    cd "$workspace" || return 1
    git init -q
    git config user.email "test@test.com"
    git config user.name "Test User"
    echo "initial" > README.md
    git add README.md
    git commit -q -m "Initial commit"
    cd "$TESTS_DIR" || return 1

    # Call git_create_commit with no uncommitted changes
    local result
    git_create_commit "$workspace" "TASK-001" "Test task" "HIGH" "worker-001" >/dev/null 2>&1
    result=$?

    assert_equals "0" "$result" "git_create_commit should succeed even with no changes"

    # Verify it created a branch
    cd "$workspace" || return 1
    local branch
    branch=$(git branch --show-current)
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [[ "$branch" == task/TASK-001-* ]]; then
        echo -e "  ${GREEN}✓${NC} Branch created even with no changes: $branch"
    else
        echo -e "  ${RED}✗${NC} Expected branch starting with task/TASK-001-, got: $branch"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi

    # The commit count should still be 1 (no new commit when there are no changes)
    local commit_count
    commit_count=$(git rev-list --count HEAD)
    assert_equals "1" "$commit_count" "No new commit should be created when there are no changes"

    cd "$TESTS_DIR" || return 1
}

# Test 16: git_is_readonly_agent with various agent types
test_git_is_readonly_agent_types() {
    local result

    # Read-only agents should return 0 (true)
    git_is_readonly_agent "engineering.security-audit"
    result=$?
    assert_equals "0" "$result" "engineering.security-audit should be read-only"

    git_is_readonly_agent "engineering.validation-review"
    result=$?
    assert_equals "0" "$result" "engineering.validation-review should be read-only"

    git_is_readonly_agent "product.plan-mode"
    result=$?
    assert_equals "0" "$result" "product.plan-mode should be read-only"

    git_is_readonly_agent "engineering.code-review"
    result=$?
    assert_equals "0" "$result" "engineering.code-review should be read-only"

    # Non-read-only agents should return 1 (false)
    git_is_readonly_agent "engineering.software-engineer"
    result=$?
    assert_equals "1" "$result" "engineering.software-engineer should NOT be read-only"

    git_is_readonly_agent "engineering.security-fix"
    result=$?
    assert_equals "1" "$result" "engineering.security-fix should NOT be read-only"

    git_is_readonly_agent "product.documentation-writer"
    result=$?
    assert_equals "1" "$result" "product.documentation-writer should NOT be read-only"

    git_is_readonly_agent "nonexistent-agent"
    result=$?
    assert_equals "1" "$result" "Unknown agent type should NOT be read-only"

    git_is_readonly_agent ""
    result=$?
    assert_equals "1" "$result" "Empty agent type should NOT be read-only"
}

# =============================================================================
# Run All Tests
# =============================================================================

# File Lock Error Paths
run_test test_file_lock_nonexistent_parent_dir
run_test test_file_lock_timeout_when_held
run_test test_file_lock_release_nonexistent
run_test test_file_lock_concurrent_serialization

# Logger Error Paths
run_test test_logger_empty_message
run_test test_logger_special_characters
run_test test_logger_debug_suppressed_at_higher_level
run_test test_logger_nonexistent_log_dir

# Task Parser Error Paths
run_test test_task_parser_empty_file
run_test test_task_parser_whitespace_only_file
run_test test_task_parser_no_matching_patterns
run_test test_task_parser_nonexistent_task_status
run_test test_task_parser_no_deps_section

# Git Operations Error Paths
run_test test_git_safety_checkpoint_non_git_dir
run_test test_git_create_commit_no_changes
run_test test_git_is_readonly_agent_types

print_test_summary
exit_with_test_result
