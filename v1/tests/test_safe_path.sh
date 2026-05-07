#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/core/safe-path.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(cd "$TESTS_DIR/.." && pwd)"

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/safe-path.sh"

# =============================================================================
# Rejection Tests (should return 1)
# =============================================================================

test_empty_string_returns_1() {
    assert_exit_code 1 "Empty string should return 1" safe_path ""
}

test_null_returns_1() {
    assert_exit_code 1 "\"null\" should return 1" safe_path "null"
}

test_root_returns_1() {
    assert_exit_code 1 "\"/\" should return 1" safe_path "/"
}

test_double_slash_returns_1() {
    assert_exit_code 1 "\"//\" should return 1" safe_path "//"
}

test_shallow_tmp_returns_1() {
    assert_exit_code 1 "\"/tmp\" (1 component) should return 1" safe_path "/tmp"
}

test_shallow_usr_returns_1() {
    assert_exit_code 1 "\"/usr\" (1 component) should return 1" safe_path "/usr"
}

# =============================================================================
# Acceptance Tests (should return 0)
# =============================================================================

test_two_component_path_returns_0() {
    assert_exit_code 0 "\"/tmp/foo\" (2 components) should return 0" safe_path "/tmp/foo"
}

test_deep_absolute_path_returns_0() {
    assert_exit_code 0 "\"/home/user/project\" should return 0" safe_path "/home/user/project"
}

test_relative_dot_slash_returns_0() {
    assert_exit_code 0 "\"./relative\" should return 0" safe_path "./relative"
}

test_relative_dot_ralph_returns_0() {
    assert_exit_code 0 "\".ralph/workers\" should return 0" safe_path ".ralph/workers"
}

test_relative_bare_returns_0() {
    assert_exit_code 0 "\"some/path\" should return 0" safe_path "some/path"
}

# =============================================================================
# Error Message Tests
# =============================================================================

test_error_message_includes_variable_name() {
    local stderr_output
    stderr_output=$(safe_path "" "RALPH_DIR" 2>&1 || true)
    assert_output_contains "$stderr_output" "RALPH_DIR" "Error message should include variable name RALPH_DIR"
}

# =============================================================================
# Run All Tests
# =============================================================================

# Rejection tests
run_test test_empty_string_returns_1
run_test test_null_returns_1
run_test test_root_returns_1
run_test test_double_slash_returns_1
run_test test_shallow_tmp_returns_1
run_test test_shallow_usr_returns_1

# Acceptance tests
run_test test_two_component_path_returns_0
run_test test_deep_absolute_path_returns_0
run_test test_relative_dot_slash_returns_0
run_test test_relative_dot_ralph_returns_0
run_test test_relative_bare_returns_0

# Error message tests
run_test test_error_message_includes_variable_name

print_test_summary
exit_with_test_result
