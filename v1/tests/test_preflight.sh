#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/core/preflight.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/exit-codes.sh"

# We can't source preflight.sh directly because it sources logger.sh which needs WIGGUM_HOME
# Instead, we'll source functions individually
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/preflight.sh"

TEST_DIR=""
setup() {
    TEST_DIR=$(mktemp -d)
    # Reset check counters (used by sourced preflight.sh functions)
    # shellcheck disable=SC2034
    CHECK_PASSED=0
    # shellcheck disable=SC2034
    CHECK_FAILED=0
    # shellcheck disable=SC2034
    CHECK_WARNED=0
}
teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# check_command_exists tests
# =============================================================================

test_check_command_exists_with_existing_command() {
    assert_success "check_command_exists should pass for 'bash'" \
        check_command_exists bash
}

test_check_command_exists_with_nonexistent_command() {
    assert_failure "check_command_exists should fail for a non-existent command" \
        check_command_exists this_command_does_not_exist_xyz_abc_123
}

# =============================================================================
# check_wiggum_home tests
# =============================================================================

test_check_wiggum_home_valid() {
    # WIGGUM_HOME is already set to the project root which has bin/, lib/, config/
    local result
    result=$(check_wiggum_home 2>&1)
    local rc=$?
    assert_equals "0" "$rc" "check_wiggum_home should pass with valid WIGGUM_HOME"
}

test_check_wiggum_home_unset() {
    (
        unset WIGGUM_HOME
        check_wiggum_home >/dev/null 2>&1
        echo $?
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "1" "$result" "check_wiggum_home should fail when WIGGUM_HOME is unset"
}

test_check_wiggum_home_missing_subdirs() {
    (
        export WIGGUM_HOME="$TEST_DIR/fake_wiggum"
        mkdir -p "$WIGGUM_HOME"
        # Only create 'bin', omit 'lib' and 'config'
        mkdir -p "$WIGGUM_HOME/bin"
        check_wiggum_home >/dev/null 2>&1
        echo $?
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "1" "$result" "check_wiggum_home should fail when required subdirs are missing"
}

# =============================================================================
# check_disk_space tests
# =============================================================================

test_check_disk_space_passes() {
    # Any modern system should have 500MB+ free
    local result
    result=$(check_disk_space "$TEST_DIR" 2>&1)
    local rc=$?
    assert_equals "0" "$rc" "check_disk_space should pass on a system with sufficient space"
}

# =============================================================================
# check_project_setup tests
# =============================================================================

test_check_project_setup_no_ralph_dir() {
    (
        export RALPH_DIR="$TEST_DIR/nonexistent_ralph"
        check_project_setup >/dev/null 2>&1
        echo $?
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "0" "$result" "check_project_setup without .ralph dir should return 0 (info, not failure)"
}

test_check_project_setup_with_ralph_and_kanban() {
    (
        export RALPH_DIR="$TEST_DIR/.ralph"
        mkdir -p "$RALPH_DIR"
        # Create a kanban.md with a task entry
        cat > "$RALPH_DIR/kanban.md" << 'KANBAN'
# Kanban

## TODO
- [x] **[TASK-1]** Setup project
- [ ] **[TASK-2]** Add feature
KANBAN
        check_project_setup >/dev/null 2>&1
        echo $?
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "0" "$result" "check_project_setup with .ralph and kanban.md should pass"

    # Also verify it increments CHECK_PASSED (run in current shell)
    export RALPH_DIR="$TEST_DIR/.ralph2"
    mkdir -p "$RALPH_DIR"
    cat > "$RALPH_DIR/kanban.md" << 'KANBAN'
- [ ] **[TASK-1]** Test task
KANBAN
    local output
    output=$(check_project_setup 2>&1)
    assert_output_contains "$output" "PASS" "Output should show PASS for valid setup"
}

test_check_project_setup_ralph_no_kanban() {
    (
        export RALPH_DIR="$TEST_DIR/.ralph_nokanban"
        mkdir -p "$RALPH_DIR"
        # No kanban.md
        check_project_setup >/dev/null 2>&1
        echo $?
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "0" "$result" "check_project_setup with .ralph but no kanban.md should return 0 (warn)"

    # Verify it prints a WARN
    export RALPH_DIR="$TEST_DIR/.ralph_nokanban2"
    mkdir -p "$RALPH_DIR"
    local output
    output=$(check_project_setup 2>&1)
    assert_output_contains "$output" "WARN" "Output should show WARN when kanban.md missing"
}

# =============================================================================
# check_config_files tests
# =============================================================================

test_check_config_files_valid_json() {
    (
        export WIGGUM_HOME="$TEST_DIR/wiggum_cfg"
        mkdir -p "$WIGGUM_HOME/config"
        echo '{"workers": {"max_iterations": 10, "sleep_seconds": 2}}' > "$WIGGUM_HOME/config/config.json"
        echo '{"agents": {}, "defaults": {"max_iterations": 10, "max_turns": 30}}' > "$WIGGUM_HOME/config/agents.json"
        # Need to re-source logger in subshell since WIGGUM_HOME changed
        source "$TESTS_DIR/../lib/core/logger.sh" 2>/dev/null || true
        check_config_files >/dev/null 2>&1
        echo $?
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "0" "$result" "check_config_files should pass with valid JSON files"
}

test_check_config_files_invalid_json() {
    (
        export WIGGUM_HOME="$TEST_DIR/wiggum_badcfg"
        mkdir -p "$WIGGUM_HOME/config"
        echo '{"key": "value"}' > "$WIGGUM_HOME/config/config.json"
        echo 'NOT VALID JSON {{{' > "$WIGGUM_HOME/config/agents.json"
        check_config_files >/dev/null 2>&1
        echo $?
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "1" "$result" "check_config_files should fail with invalid JSON"
}

# =============================================================================
# check_path tests
# =============================================================================

test_check_path_in_path() {
    (
        export PATH="$WIGGUM_HOME/bin:$PATH"
        check_path >/dev/null 2>&1
        echo $?
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "0" "$result" "check_path should pass when WIGGUM_HOME/bin is in PATH"
}

test_check_path_not_in_path() {
    (
        # Strip WIGGUM_HOME/bin from PATH
        export PATH="/usr/bin:/usr/local/bin:/bin"
        check_path >/dev/null 2>&1
        echo $?
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "1" "$result" "check_path should fail when WIGGUM_HOME/bin is NOT in PATH"
}

# =============================================================================
# check_jq tests
# =============================================================================

test_check_jq_passes() {
    local result
    result=$(check_jq 2>&1)
    local rc=$?
    assert_equals "0" "$rc" "check_jq should pass (jq is required for this project)"
}

# =============================================================================
# check_git tests
# =============================================================================

test_check_git_passes() {
    local result
    result=$(check_git 2>&1)
    local rc=$?
    assert_equals "0" "$rc" "check_git should pass (git 2.5+ is required)"
}

# =============================================================================
# check_timeout tests
# =============================================================================

test_check_timeout_passes() {
    local result
    result=$(check_timeout 2>&1)
    local rc=$?
    assert_equals "0" "$rc" "check_timeout should pass (timeout is available on this system)"
}

# =============================================================================
# check_posix_utilities tests
# =============================================================================

test_check_posix_utilities_passes() {
    local result
    result=$(check_posix_utilities 2>&1)
    local rc=$?
    assert_equals "0" "$rc" "check_posix_utilities should pass on a normal system"
}

# =============================================================================
# Run all tests
# =============================================================================

run_test test_check_command_exists_with_existing_command
run_test test_check_command_exists_with_nonexistent_command
run_test test_check_wiggum_home_valid
run_test test_check_wiggum_home_unset
run_test test_check_wiggum_home_missing_subdirs
run_test test_check_disk_space_passes
run_test test_check_project_setup_no_ralph_dir
run_test test_check_project_setup_with_ralph_and_kanban
run_test test_check_project_setup_ralph_no_kanban
run_test test_check_config_files_valid_json
run_test test_check_config_files_invalid_json
run_test test_check_path_in_path
run_test test_check_path_not_in_path
run_test test_check_jq_passes
run_test test_check_git_passes
run_test test_check_timeout_passes
run_test test_check_posix_utilities_passes

print_test_summary
exit_with_test_result
