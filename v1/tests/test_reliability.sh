#!/usr/bin/env bash
set -euo pipefail
# test_reliability.sh - Tests for reliability improvements (P0 fixes)

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"

LOG_LEVEL=ERROR
export LOG_LEVEL

# =============================================================================
# lib/core/process.sh Tests
# =============================================================================

test_wait_safe_captures_zero_exit() {
    source "$WIGGUM_HOME/lib/core/process.sh"

    # Use file redirection instead of $() — command substitution creates a
    # subshell where wait can't see the parent's background PID (returns 127).
    local tmpfile
    tmpfile=$(mktemp)
    (exit 0) &
    local pid=$!
    wait_safe "$pid" > "$tmpfile"
    local exit_code
    exit_code=$(cat "$tmpfile")
    rm -f "$tmpfile"

    assert_equals "0" "$exit_code" "wait_safe should capture exit code 0"
}

test_wait_safe_captures_nonzero_exit() {
    source "$WIGGUM_HOME/lib/core/process.sh"

    local tmpfile
    tmpfile=$(mktemp)
    (exit 42) &
    local pid=$!
    wait_safe "$pid" > "$tmpfile"
    local exit_code
    exit_code=$(cat "$tmpfile")
    rm -f "$tmpfile"

    assert_equals "42" "$exit_code" "wait_safe should capture exit code 42"
}

test_wait_safe_var_stores_in_variable() {
    source "$WIGGUM_HOME/lib/core/process.sh"

    (exit 7) &
    local pid=$!
    local result=0
    wait_safe_var result "$pid"

    assert_equals "7" "$result" "wait_safe_var should store exit code in variable"
}

test_kill_safe_succeeds_on_dead_process() {
    source "$WIGGUM_HOME/lib/core/process.sh"

    # Use a PID that definitely doesn't exist
    local fake_pid=99999999

    # Should not error even though process doesn't exist
    local result=0
    kill_safe "$fake_pid" || result=$?

    assert_equals "0" "$result" "kill_safe should return 0 for non-existent process"
}

test_is_process_running_detects_dead() {
    source "$WIGGUM_HOME/lib/core/process.sh"

    local fake_pid=99999999
    local result=0
    is_process_running "$fake_pid" || result=$?

    assert_equals "1" "$result" "is_process_running should return 1 for dead process"
}

test_run_capturing_exit_captures_failure() {
    source "$WIGGUM_HOME/lib/core/process.sh"

    local exit_code
    exit_code=$(run_capturing_exit false)

    assert_equals "1" "$exit_code" "run_capturing_exit should capture 'false' exit code"
}

test_run_capturing_exit_var() {
    source "$WIGGUM_HOME/lib/core/process.sh"

    local rc=0
    run_capturing_exit_var rc false

    assert_equals "1" "$rc" "run_capturing_exit_var should store exit code"
}

# =============================================================================
# lib/service/service-handler-common.sh Tests
# =============================================================================

test_svc_require_env_passes_when_set() {
    source "$WIGGUM_HOME/lib/service/service-handler-common.sh"

    export TEST_VAR_ONE="value1"
    export TEST_VAR_TWO="value2"

    local result=0
    svc_require_env TEST_VAR_ONE TEST_VAR_TWO || result=$?

    unset TEST_VAR_ONE TEST_VAR_TWO

    assert_equals "0" "$result" "svc_require_env should pass when all vars set"
}

test_svc_require_env_fails_when_missing() {
    source "$WIGGUM_HOME/lib/service/service-handler-common.sh"

    export TEST_VAR_ONE="value1"
    unset TEST_VAR_MISSING 2>/dev/null || true

    local result=0
    svc_require_env TEST_VAR_ONE TEST_VAR_MISSING 2>/dev/null || result=$?

    unset TEST_VAR_ONE

    assert_equals "1" "$result" "svc_require_env should fail when var missing"
}

test_svc_require_files_passes_when_exist() {
    source "$WIGGUM_HOME/lib/service/service-handler-common.sh"

    local temp_file
    temp_file=$(mktemp)

    local result=0
    svc_require_files "$temp_file" || result=$?

    rm -f "$temp_file"

    assert_equals "0" "$result" "svc_require_files should pass when file exists"
}

test_svc_require_files_fails_when_missing() {
    source "$WIGGUM_HOME/lib/service/service-handler-common.sh"

    local result=0
    svc_require_files "/nonexistent/file/path" 2>/dev/null || result=$?

    assert_equals "1" "$result" "svc_require_files should fail when file missing"
}

test_svc_run_if_runs_when_true() {
    source "$WIGGUM_HOME/lib/service/service-handler-common.sh"

    _test_func_called=false
    _test_func() { _test_func_called=true; }

    export CONDITION_VAR="true"
    svc_run_if CONDITION_VAR _test_func

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ "$_test_func_called" = "true" ]; then
        echo -e "  ${GREEN}✓${NC} svc_run_if runs function when condition true"
    else
        echo -e "  ${RED}✗${NC} svc_run_if should run function when condition true"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

test_svc_run_if_skips_when_false() {
    source "$WIGGUM_HOME/lib/service/service-handler-common.sh"

    _test_func_called=false
    _test_func() { _test_func_called=true; }

    export CONDITION_VAR="false"
    svc_run_if CONDITION_VAR _test_func

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ "$_test_func_called" = "false" ]; then
        echo -e "  ${GREEN}✓${NC} svc_run_if skips function when condition false"
    else
        echo -e "  ${RED}✗${NC} svc_run_if should skip function when condition false"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

test_svc_try_returns_zero_on_failure() {
    source "$WIGGUM_HOME/lib/service/service-handler-common.sh"

    _failing_func() { return 1; }

    local result=0
    svc_try "test" _failing_func 2>/dev/null || result=$?

    assert_equals "0" "$result" "svc_try should return 0 even when function fails"
}

test_svc_run_if_any_runs_on_first_true() {
    source "$WIGGUM_HOME/lib/service/service-handler-common.sh"

    _test_func_called=false
    _test_func() { _test_func_called=true; }

    export COND_A="false"
    export COND_B="true"
    export COND_C="false"
    svc_run_if_any _test_func COND_A COND_B COND_C

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ "$_test_func_called" = "true" ]; then
        echo -e "  ${GREEN}✓${NC} svc_run_if_any runs when any condition true"
    else
        echo -e "  ${RED}✗${NC} svc_run_if_any should run when any condition true"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

# =============================================================================
# lib/core/safe-path.sh Tests
# =============================================================================

test_safe_path_rejects_empty() {
    source "$WIGGUM_HOME/lib/core/safe-path.sh"

    local result=0
    safe_path "" "test_var" 2>/dev/null || result=$?

    assert_equals "1" "$result" "safe_path should reject empty path"
}

test_safe_path_rejects_root() {
    source "$WIGGUM_HOME/lib/core/safe-path.sh"

    local result=0
    safe_path "/" "test_var" 2>/dev/null || result=$?

    assert_equals "1" "$result" "safe_path should reject root path"
}

test_safe_path_rejects_shallow() {
    source "$WIGGUM_HOME/lib/core/safe-path.sh"

    local result=0
    safe_path "/tmp" "test_var" 2>/dev/null || result=$?

    assert_equals "1" "$result" "safe_path should reject shallow path"
}

test_safe_path_accepts_valid() {
    source "$WIGGUM_HOME/lib/core/safe-path.sh"

    local result=0
    safe_path "/home/user/project" "test_var" || result=$?

    assert_equals "0" "$result" "safe_path should accept valid path"
}

# =============================================================================
# lib/core/gh-error.sh Tests
# =============================================================================

test_gh_is_network_error_detects_timeout() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    local result=0
    gh_is_network_error "124" "" || result=$?

    assert_equals "0" "$result" "gh_is_network_error should detect timeout (124)"
}

test_gh_is_network_error_detects_connection_refused() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    local result=0
    gh_is_network_error "1" "Connection refused" || result=$?

    assert_equals "0" "$result" "gh_is_network_error should detect connection refused"
}

test_gh_is_network_error_rejects_auth_error() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    local result=0
    gh_is_network_error "1" "401 Unauthorized" || result=$?

    assert_equals "1" "$result" "gh_is_network_error should not treat auth errors as network"
}

# =============================================================================
# Run All Tests
# =============================================================================

echo "=== Reliability Tests (P0 Fixes) ==="

# Process module tests
run_test test_wait_safe_captures_zero_exit
run_test test_wait_safe_captures_nonzero_exit
run_test test_wait_safe_var_stores_in_variable
run_test test_kill_safe_succeeds_on_dead_process
run_test test_is_process_running_detects_dead
run_test test_run_capturing_exit_captures_failure
run_test test_run_capturing_exit_var

# Service handler common tests
run_test test_svc_require_env_passes_when_set
run_test test_svc_require_env_fails_when_missing
run_test test_svc_require_files_passes_when_exist
run_test test_svc_require_files_fails_when_missing
run_test test_svc_run_if_runs_when_true
run_test test_svc_run_if_skips_when_false
run_test test_svc_try_returns_zero_on_failure
run_test test_svc_run_if_any_runs_on_first_true

# Safe path tests
run_test test_safe_path_rejects_empty
run_test test_safe_path_rejects_root
run_test test_safe_path_rejects_shallow
run_test test_safe_path_accepts_valid

# GH error tests
run_test test_gh_is_network_error_detects_timeout
run_test test_gh_is_network_error_detects_connection_refused
run_test test_gh_is_network_error_rejects_auth_error

print_test_summary
exit_with_test_result
