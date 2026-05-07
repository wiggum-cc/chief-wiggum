#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/core/logger.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"

# Create temp dir for log file tests
TEST_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    # Reset log-related env vars
    unset LOG_LEVEL
    unset LOG_FILE
    unset DEBUG
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
    unset LOG_LEVEL
    unset LOG_FILE
    unset DEBUG
}

# =============================================================================
# _log_level_value() Tests
# =============================================================================

test_log_level_value_trace() {
    local val
    val=$(_log_level_value "TRACE")
    assert_equals "0" "$val" "TRACE should have value 0"
}

test_log_level_value_debug() {
    local val
    val=$(_log_level_value "DEBUG")
    assert_equals "1" "$val" "DEBUG should have value 1"
}

test_log_level_value_info() {
    local val
    val=$(_log_level_value "INFO")
    assert_equals "2" "$val" "INFO should have value 2"
}

test_log_level_value_warn() {
    local val
    val=$(_log_level_value "WARN")
    assert_equals "3" "$val" "WARN should have value 3"
}

test_log_level_value_error() {
    local val
    val=$(_log_level_value "ERROR")
    assert_equals "4" "$val" "ERROR should have value 4"
}

test_log_level_value_unknown_defaults_to_info() {
    local val
    val=$(_log_level_value "UNKNOWN")
    assert_equals "2" "$val" "Unknown level should default to INFO (2)"
}

# =============================================================================
# _should_log() Tests
# =============================================================================

test_should_log_default_level_is_info() {
    # Default should be INFO, so DEBUG should not log
    if _should_log "DEBUG"; then
        echo -e "  ${RED}X${NC} DEBUG should not log at default INFO level"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} DEBUG correctly filtered at INFO level"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    # INFO should log
    if _should_log "INFO"; then
        echo -e "  ${GREEN}✓${NC} INFO logs at INFO level"
    else
        echo -e "  ${RED}X${NC} INFO should log at INFO level"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_should_log_debug_env_enables_debug() {
    export DEBUG=1
    if _should_log "DEBUG"; then
        echo -e "  ${GREEN}✓${NC} DEBUG logs when DEBUG=1"
    else
        echo -e "  ${RED}X${NC} DEBUG should log when DEBUG=1"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_should_log_log_level_env() {
    export LOG_LEVEL=WARN

    # INFO should NOT log at WARN level
    if _should_log "INFO"; then
        echo -e "  ${RED}X${NC} INFO should not log at WARN level"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} INFO correctly filtered at WARN level"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    # WARN should log
    if _should_log "WARN"; then
        echo -e "  ${GREEN}✓${NC} WARN logs at WARN level"
    else
        echo -e "  ${RED}X${NC} WARN should log at WARN level"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    # ERROR should log
    if _should_log "ERROR"; then
        echo -e "  ${GREEN}✓${NC} ERROR logs at WARN level"
    else
        echo -e "  ${RED}X${NC} ERROR should log at WARN level"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# log() / log_info() Tests
# =============================================================================

test_log_info_includes_timestamp() {
    local output
    output=$(log "test message" 2>&1)
    assert_output_contains "$output" "INFO:" "log() should include INFO level"
    # Check for ISO timestamp pattern
    if echo "$output" | grep -qE '\[[0-9]{4}-[0-9]{2}-[0-9]{2}'; then
        echo -e "  ${GREEN}✓${NC} Output includes timestamp"
    else
        echo -e "  ${RED}X${NC} Output should include timestamp"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_log_info_alias() {
    local output
    output=$(log_info "test message" 2>&1)
    assert_output_contains "$output" "INFO:" "log_info() should include INFO level"
}

# =============================================================================
# log_warn() Tests
# =============================================================================

test_log_warn_to_stderr() {
    local stderr_output
    # Capture stderr only
    stderr_output=$(log_warn "warning message" 2>&1 1>/dev/null)
    assert_output_contains "$stderr_output" "WARN:" "log_warn() should output WARN to stderr"
}

# =============================================================================
# log_error() Tests
# =============================================================================

test_log_error_to_stderr() {
    local stderr_output
    stderr_output=$(log_error "error message" 2>&1 1>/dev/null)
    assert_output_contains "$stderr_output" "ERROR:" "log_error() should output ERROR to stderr"
}

# =============================================================================
# log_debug() Tests
# =============================================================================

test_log_debug_filtered_by_default() {
    local output
    output=$(log_debug "debug message" 2>&1)
    assert_equals "" "$output" "log_debug() should produce no output at default level"
}

test_log_debug_enabled_with_debug_flag() {
    export DEBUG=1
    local output
    output=$(log_debug "debug message" 2>&1)
    assert_output_contains "$output" "DEBUG:" "log_debug() should output when DEBUG=1"
}

test_log_debug_enabled_with_log_level() {
    export LOG_LEVEL=DEBUG
    local output
    output=$(log_debug "debug message" 2>&1)
    assert_output_contains "$output" "DEBUG:" "log_debug() should output when LOG_LEVEL=DEBUG"
}

# =============================================================================
# log_trace() Tests
# =============================================================================

test_log_trace_filtered_by_default() {
    local output
    output=$(log_trace "trace message" 2>&1)
    assert_equals "" "$output" "log_trace() should produce no output at default level"
}

test_log_trace_filtered_at_debug_level() {
    export LOG_LEVEL=DEBUG
    local output
    output=$(log_trace "trace message" 2>&1)
    assert_equals "" "$output" "log_trace() should not output at DEBUG level"
}

test_log_trace_enabled_with_log_level() {
    export LOG_LEVEL=TRACE
    local output
    output=$(log_trace "trace message" 2>&1)
    assert_output_contains "$output" "TRACE:" "log_trace() should output when LOG_LEVEL=TRACE"
}

# =============================================================================
# LOG_FILE Tests
# =============================================================================

test_log_file_appends() {
    local log_file="$TEST_DIR/test.log"
    export LOG_FILE="$log_file"

    log "first message" > /dev/null 2>&1
    log "second message" > /dev/null 2>&1

    assert_file_exists "$log_file" "Log file should be created"
    assert_file_contains "$log_file" "first message" "Log file should contain first message"
    assert_file_contains "$log_file" "second message" "Log file should contain second message"
}

test_log_file_includes_all_levels() {
    local log_file="$TEST_DIR/all_levels.log"
    export LOG_FILE="$log_file"
    export LOG_LEVEL=TRACE

    log_trace "trace msg" 2>/dev/null
    log_debug "debug msg" 2>/dev/null
    log_info "info msg" 2>/dev/null
    log_warn "warn msg" 2>/dev/null
    log_error "error msg" 2>/dev/null

    assert_file_contains "$log_file" "TRACE:" "Log file should contain TRACE"
    assert_file_contains "$log_file" "DEBUG:" "Log file should contain DEBUG"
    assert_file_contains "$log_file" "INFO:" "Log file should contain INFO"
    assert_file_contains "$log_file" "WARN:" "Log file should contain WARN"
    assert_file_contains "$log_file" "ERROR:" "Log file should contain ERROR"
}

# =============================================================================
# Run All Tests
# =============================================================================

# _log_level_value tests
run_test test_log_level_value_trace
run_test test_log_level_value_debug
run_test test_log_level_value_info
run_test test_log_level_value_warn
run_test test_log_level_value_error
run_test test_log_level_value_unknown_defaults_to_info

# _should_log tests
run_test test_should_log_default_level_is_info
run_test test_should_log_debug_env_enables_debug
run_test test_should_log_log_level_env

# log/log_info tests
run_test test_log_info_includes_timestamp
run_test test_log_info_alias

# log_warn tests
run_test test_log_warn_to_stderr

# log_error tests
run_test test_log_error_to_stderr

# log_debug tests
run_test test_log_debug_filtered_by_default
run_test test_log_debug_enabled_with_debug_flag
run_test test_log_debug_enabled_with_log_level

# log_trace tests
run_test test_log_trace_filtered_by_default
run_test test_log_trace_filtered_at_debug_level
run_test test_log_trace_enabled_with_log_level

# LOG_FILE tests
run_test test_log_file_appends
run_test test_log_file_includes_all_levels

print_test_summary
exit_with_test_result
