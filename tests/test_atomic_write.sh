#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/core/atomic-write.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(cd "$TESTS_DIR/.." && pwd)"

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/atomic-write.sh"

# Test temp directory
_AW_TEST_DIR=""

setup() {
    _AW_TEST_DIR=$(mktemp -d /tmp/wiggum-test-aw-XXXXXX)
}

teardown() {
    [ -n "$_AW_TEST_DIR" ] && rm -rf "$_AW_TEST_DIR"
}

# =============================================================================
# Command Mode Tests
# =============================================================================

test_command_mode_creates_file() {
    setup
    atomic_write "$_AW_TEST_DIR/out.json" jq -n '{key: "value"}'
    local actual
    actual=$(jq -r '.key' "$_AW_TEST_DIR/out.json")
    assert_equals "value" "$actual" "Command mode should write jq output"
    teardown
}

test_command_mode_overwrites_existing() {
    setup
    echo '{"old": true}' > "$_AW_TEST_DIR/out.json"
    atomic_write "$_AW_TEST_DIR/out.json" jq -n '{new: true}'
    local actual
    actual=$(jq -r '.new' "$_AW_TEST_DIR/out.json")
    assert_equals "true" "$actual" "Command mode should overwrite existing file"
    teardown
}

test_command_mode_creates_parent_dir() {
    setup
    atomic_write "$_AW_TEST_DIR/sub/dir/out.json" jq -n '{nested: true}'
    assert_file_exists "$_AW_TEST_DIR/sub/dir/out.json"
    teardown
}

test_command_mode_failure_no_partial_file() {
    setup
    # false always exits 1
    local rc=0
    atomic_write "$_AW_TEST_DIR/out.json" false || rc=$?
    assert_not_equals "0" "$rc" "Command failure should propagate"
    assert_file_not_exists "$_AW_TEST_DIR/out.json" "Failed write should not leave target"
    teardown
}

test_command_mode_no_temp_files_left() {
    setup
    atomic_write "$_AW_TEST_DIR/out.json" jq -n '{ok: true}'
    local leftover
    leftover=$(find "$_AW_TEST_DIR" -name 'out.json.*' 2>/dev/null | wc -l)
    leftover="${leftover// /}"
    assert_equals "0" "$leftover" "No temp files should remain after success"
    teardown
}

# =============================================================================
# Pipe Mode Tests
# =============================================================================

test_pipe_mode_creates_file() {
    setup
    echo '{"piped": true}' | atomic_write "$_AW_TEST_DIR/piped.json"
    local actual
    actual=$(jq -r '.piped' "$_AW_TEST_DIR/piped.json")
    assert_equals "true" "$actual" "Pipe mode should write stdin"
    teardown
}

test_pipe_mode_multiline() {
    setup
    printf 'line1\nline2\nline3\n' | atomic_write "$_AW_TEST_DIR/lines.txt"
    local count
    count=$(wc -l < "$_AW_TEST_DIR/lines.txt")
    count="${count// /}"
    assert_equals "3" "$count" "Pipe mode should preserve multi-line content"
    teardown
}

# =============================================================================
# Run All Tests
# =============================================================================

run_test test_command_mode_creates_file
run_test test_command_mode_overwrites_existing
run_test test_command_mode_creates_parent_dir
run_test test_command_mode_failure_no_partial_file
run_test test_command_mode_no_temp_files_left
run_test test_pipe_mode_creates_file
run_test test_pipe_mode_multiline

print_test_summary
exit_with_test_result
