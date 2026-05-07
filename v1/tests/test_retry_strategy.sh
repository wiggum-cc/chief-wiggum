#!/usr/bin/env bash
# test_retry_strategy.sh - Tests for runtime retry and error classification
#
# Validates that runtime_exec_with_retry correctly detects HTTP 429 rate-limit
# errors surfacing as exit code 1 by inspecting stderr output.

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$TESTS_DIR/test-framework.sh"
source "$TESTS_DIR/mocks/mock-helpers.sh"

# We need WIGGUM_HOME set for sourcing runtime
export WIGGUM_HOME="${WIGGUM_HOME:-$(cd "$TESTS_DIR/.." && pwd)}"

# Source the module under test
source "$WIGGUM_HOME/lib/runtime/runtime.sh"

# =============================================================================
# Setup / Teardown
# =============================================================================

setup() {
    mock_setup
    # Use fast backoffs for tests
    export WIGGUM_RUNTIME_MAX_RETRIES=2
    export WIGGUM_RUNTIME_INITIAL_BACKOFF=0
    export WIGGUM_RUNTIME_MAX_BACKOFF=0
}

teardown() {
    mock_teardown
    unset WIGGUM_RUNTIME_MAX_RETRIES
    unset WIGGUM_RUNTIME_INITIAL_BACKOFF
    unset WIGGUM_RUNTIME_MAX_BACKOFF
    unset RETRY_COUNTER_FILE
}

# =============================================================================
# Unit tests: runtime_backend_is_retryable
# =============================================================================

test_is_retryable_with_429() {
    local tmp
    tmp=$(mktemp)
    echo "Error: HTTP 429 Too Many Requests" > "$tmp"
    runtime_backend_is_retryable 1 "$tmp"
    local result=$?
    rm -f "$tmp"
    assert_equals "0" "$result" "Should detect '429' in stderr"
}

test_is_retryable_with_rate_limit() {
    local tmp
    tmp=$(mktemp)
    echo "rate limit exceeded, please retry" > "$tmp"
    runtime_backend_is_retryable 1 "$tmp"
    local result=$?
    rm -f "$tmp"
    assert_equals "0" "$result" "Should detect 'rate limit' in stderr"
}

test_is_retryable_with_too_many_requests() {
    local tmp
    tmp=$(mktemp)
    echo "Too Many Requests" > "$tmp"
    runtime_backend_is_retryable 1 "$tmp"
    local result=$?
    rm -f "$tmp"
    assert_equals "0" "$result" "Should detect 'too many requests' (case-insensitive)"
}

test_is_retryable_with_high_concurrency() {
    local tmp
    tmp=$(mktemp)
    echo "High concurrency detected" > "$tmp"
    runtime_backend_is_retryable 1 "$tmp"
    local result=$?
    rm -f "$tmp"
    assert_equals "0" "$result" "Should detect 'High concurrency' in stderr"
}

test_is_retryable_no_match() {
    local tmp
    tmp=$(mktemp)
    echo "Something went wrong" > "$tmp"
    local result=0
    runtime_backend_is_retryable 1 "$tmp" || result=$?
    rm -f "$tmp"
    assert_equals "1" "$result" "Should return 1 when no rate-limit pattern found"
}

test_is_retryable_empty_file() {
    local tmp
    tmp=$(mktemp)
    : > "$tmp"
    local result=0
    runtime_backend_is_retryable 1 "$tmp" || result=$?
    rm -f "$tmp"
    assert_equals "1" "$result" "Should return 1 for empty file"
}

# =============================================================================
# Integration tests: runtime_exec_with_retry
# =============================================================================

test_no_retry_on_plain_exit_1() {
    # Exit code 1 with no rate-limit stderr should NOT retry
    export MOCK_CLAUDE_EXIT_CODE=1
    local exit_code=0
    runtime_exec_with_retry -p "test" > /dev/null 2>&1 || exit_code=$?
    assert_equals "1" "$exit_code" "Should return exit code 1"
    assert_mock_invocation_count "1" "Should invoke claude exactly once (no retry)"
}

test_retry_on_exit_1_with_429_stderr() {
    # Exit code 1 + "429" stderr should trigger retry
    export MOCK_CLAUDE_EXIT_CODE=1
    export MOCK_CLAUDE_STDERR="Error: HTTP 429 Too Many Requests"
    local exit_code=0
    runtime_exec_with_retry -p "test" > /dev/null 2>&1 || exit_code=$?
    assert_equals "1" "$exit_code" "Should still ultimately return exit 1 after exhausting retries"
    local count
    count=$(mock_get_invocation_count)
    assert_greater_than "$count" 1 "Should have retried (invocations > 1)"
}

test_retry_on_exit_1_with_high_concurrency_stderr() {
    # Exit code 1 + "High concurrency" stderr should trigger retry
    export MOCK_CLAUDE_EXIT_CODE=1
    export MOCK_CLAUDE_STDERR="High concurrency detected, please slow down"
    local exit_code=0
    runtime_exec_with_retry -p "test" > /dev/null 2>&1 || exit_code=$?
    assert_equals "1" "$exit_code" "Should still ultimately return exit 1"
    local count
    count=$(mock_get_invocation_count)
    assert_greater_than "$count" 1 "Should have retried (invocations > 1)"
}

test_retry_on_exit_5() {
    # Existing behavior: exit code 5 always retries
    export MOCK_CLAUDE_EXIT_CODE=5
    local exit_code=0
    runtime_exec_with_retry -p "test" > /dev/null 2>&1 || exit_code=$?
    assert_equals "5" "$exit_code" "Should return exit code 5"
    local count
    count=$(mock_get_invocation_count)
    assert_greater_than "$count" 1 "Should have retried on exit 5"
}

test_success_after_rate_limit() {
    # First call fails with 429 stderr, second call succeeds
    # Use a custom mock script with a counter file
    local counter_file="$MOCK_DIR/retry-counter"
    echo "0" > "$counter_file"

    local mock_script="$MOCK_DIR/retry-mock.sh"
    cat > "$mock_script" << 'MOCKEOF'
#!/usr/bin/env bash
count=$(cat "$RETRY_COUNTER_FILE")
count=$((count + 1))
echo "$count" > "$RETRY_COUNTER_FILE"
if [ "$count" -le 1 ]; then
    echo "HTTP 429 Too Many Requests" >&2
    exit 1
fi
echo "OK"
exit 0
MOCKEOF
    chmod +x "$mock_script"

    export CLAUDE="$mock_script"
    export RETRY_COUNTER_FILE="$counter_file"

    local exit_code=0
    runtime_exec_with_retry -p "test" > /dev/null 2>&1 || exit_code=$?
    assert_equals "0" "$exit_code" "Should succeed on second attempt"
}

test_exhausted_retries_rate_limit() {
    # All attempts fail with exit 1 + 429 stderr
    export MOCK_CLAUDE_EXIT_CODE=1
    export MOCK_CLAUDE_STDERR="429 rate limit hit"
    export WIGGUM_RUNTIME_MAX_RETRIES=2

    local exit_code=0
    runtime_exec_with_retry -p "test" > /dev/null 2>&1 || exit_code=$?
    assert_equals "1" "$exit_code" "Should return exit 1 after exhausting retries"

    # max_retries=2 means initial attempt + 2 retries = 3 total
    assert_mock_invocation_count "3" "Should have 3 total invocations (1 initial + 2 retries)"
}

# =============================================================================
# Run all tests
# =============================================================================

run_test test_is_retryable_with_429
run_test test_is_retryable_with_rate_limit
run_test test_is_retryable_with_too_many_requests
run_test test_is_retryable_with_high_concurrency
run_test test_is_retryable_no_match
run_test test_is_retryable_empty_file

run_test test_no_retry_on_plain_exit_1
run_test test_retry_on_exit_1_with_429_stderr
run_test test_retry_on_exit_1_with_high_concurrency_stderr
run_test test_retry_on_exit_5
run_test test_success_after_rate_limit
run_test test_exhausted_retries_rate_limit

print_test_summary
exit_with_test_result
