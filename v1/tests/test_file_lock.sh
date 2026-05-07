#!/usr/bin/env bash
set -euo pipefail
# Test file-lock.sh with edge cases including special characters

set -e

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"

TEST_DIR=""
setup() {
    TEST_DIR=$(mktemp -d)
}
teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# Test 1: Basic locking with simple command
test_basic_file_lock() {
    local test_file="$TEST_DIR/test1.txt"
    with_file_lock "$test_file" 5 echo "Hello World" > "$test_file"

    assert_file_exists "$test_file" "Lock file should be created"
    assert_file_contains "$test_file" "Hello World" "File should contain the echoed text"
}

# Test 2: Special characters in file content
test_special_characters() {
    local test_file="$TEST_DIR/test2.txt"
    with_file_lock "$test_file" 5 bash -c 'echo "Special chars: $ \" \` \\ ; | & > <" > "$1"' _ "$test_file"

    assert_file_exists "$test_file" "File with special chars should exist"
    assert_file_contains "$test_file" 'Special chars:' "File should contain special character content"
}

# Test 3: Update kanban status with special task ID
test_update_kanban_status() {
    local kanban_file="$TEST_DIR/kanban.md"
    cat > "$kanban_file" << 'EOF'
# Kanban Board

- [ ] **[TASK-001]** Test task one
- [ ] **[TASK-002]** Test task with special chars: $var
- [ ] **[TASK-003]** Another task
EOF

    update_kanban_status "$kanban_file" "TASK-002" "x"
    assert_file_contains "$kanban_file" '- [x] **[TASK-002]**' \
        "TASK-002 should be marked as completed"
}

# Test 4: Concurrent access (spawn multiple processes)
test_concurrent_file_access() {
    local concurrent_file="$TEST_DIR/concurrent.txt"
    echo "0" > "$concurrent_file"

    for _ in {1..5}; do
        (
            with_file_lock "$concurrent_file" 10 bash -c '
                current=$(cat "$1")
                new=$((current + 1))
                echo "$new" > "$1"
            ' _ "$concurrent_file"
        ) &
    done

    wait

    local final_count
    final_count=$(cat "$concurrent_file")
    assert_equals "5" "$final_count" "Concurrent lock should serialize to exactly 5"
}

# Test 5: Changelog append with special characters
test_changelog_append_special_chars() {
    local changelog_file="$TEST_DIR/changelog.md"
    touch "$changelog_file"

    append_changelog "$changelog_file" "TASK-999" "worker-1" \
        'Fix bug with special chars: $ " ` \' \
        "https://github.com/test/pr/1" \
        'Summary with special chars: & | > < ;'

    assert_file_exists "$changelog_file" "Changelog file should exist"
    assert_file_contains "$changelog_file" 'TASK-999' "Changelog should contain task ID"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_basic_file_lock
run_test test_special_characters
run_test test_update_kanban_status
run_test test_concurrent_file_access
run_test test_changelog_append_special_chars

print_test_summary
exit_with_test_result
