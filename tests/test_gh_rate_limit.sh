#!/usr/bin/env bash
# test_gh_rate_limit.sh - Tests for GitHub API rate limit detection and guard

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$TESTS_DIR/test-framework.sh"

# Set up WIGGUM_HOME for sourcing
export WIGGUM_HOME="${TESTS_DIR}/.."

# Source the modules under test
source "$WIGGUM_HOME/lib/core/gh-error.sh"

# =============================================================================
# gh_is_rate_limit_error tests
# =============================================================================

test_rate_limit_detects_primary_rate_limit() {
    assert_success "Detects 'API rate limit exceeded'" \
        gh_is_rate_limit_error "" "API rate limit exceeded for user ID 12345"

    assert_success "Detects 'rate limit exceeded'" \
        gh_is_rate_limit_error "" "rate limit exceeded"
}

test_rate_limit_detects_secondary_rate_limit() {
    assert_success "Detects 'secondary rate limit'" \
        gh_is_rate_limit_error "" "You have exceeded a secondary rate limit. Please wait a few minutes."
}

test_rate_limit_detects_http_429() {
    assert_success "Detects 'HTTP 429'" \
        gh_is_rate_limit_error "" "HTTP 429"

    assert_success "Detects '429 Too Many Requests'" \
        gh_is_rate_limit_error "" "429 Too Many Requests"
}

test_rate_limit_detects_abuse() {
    assert_success "Detects 'abuse detection'" \
        gh_is_rate_limit_error "" "abuse detection mechanism"
}

test_rate_limit_rejects_non_rate_limit() {
    assert_failure "Rejects normal error" \
        gh_is_rate_limit_error "1" "Not found"

    assert_failure "Rejects network error" \
        gh_is_rate_limit_error "" "Connection refused"

    assert_failure "Rejects empty" \
        gh_is_rate_limit_error "" ""
}

# =============================================================================
# gh_is_network_error includes rate limit patterns
# =============================================================================

test_network_error_includes_rate_limits() {
    assert_success "Network error includes HTTP 429" \
        gh_is_network_error "" "HTTP 429"

    assert_success "Network error includes 'API rate limit exceeded'" \
        gh_is_network_error "" "API rate limit exceeded"

    assert_success "Network error includes 'secondary rate limit'" \
        gh_is_network_error "" "secondary rate limit"
}

# =============================================================================
# gh_format_error rate limit messages
# =============================================================================

test_format_error_rate_limit() {
    local msg
    msg=$(gh_format_error "1" "API rate limit exceeded" "listing issues")
    assert_output_contains "$msg" "rate limited" "Format error mentions rate limited"
    assert_output_contains "$msg" "listing issues" "Format error includes operation"
}

test_format_error_network_not_rate_limit() {
    local msg
    msg=$(gh_format_error "1" "Connection refused" "fetching PRs")
    assert_output_contains "$msg" "Network error" "Format error shows network error"
}

# =============================================================================
# GH_LAST_WAS_RATE_LIMIT flag
# =============================================================================

test_global_rate_limit_flag_initialized() {
    assert_equals "false" "$GH_LAST_WAS_RATE_LIMIT" "GH_LAST_WAS_RATE_LIMIT starts false"
}

# =============================================================================
# gh_with_network_detection sets rate limit flag
# =============================================================================

test_with_detection_sets_rate_limit_flag() {
    # Create a fake command that outputs rate limit error
    local fake_cmd
    fake_cmd=$(mktemp)
    cat > "$fake_cmd" << 'SCRIPT'
#!/usr/bin/env bash
echo "API rate limit exceeded for user" >&2
exit 1
SCRIPT
    chmod +x "$fake_cmd"

    gh_with_network_detection "$fake_cmd" > /dev/null 2>&1 || true

    assert_equals "true" "$GH_LAST_WAS_RATE_LIMIT" "Rate limit flag set on rate limit error"
    assert_equals "true" "$GH_LAST_WAS_NETWORK_ERROR" "Network error flag also set on rate limit"

    rm -f "$fake_cmd"
}

test_with_detection_no_rate_limit_on_network_error() {
    local fake_cmd
    fake_cmd=$(mktemp)
    cat > "$fake_cmd" << 'SCRIPT'
#!/usr/bin/env bash
echo "Connection refused" >&2
exit 1
SCRIPT
    chmod +x "$fake_cmd"

    gh_with_network_detection "$fake_cmd" > /dev/null 2>&1 || true

    assert_equals "false" "$GH_LAST_WAS_RATE_LIMIT" "Rate limit flag NOT set on network error"
    assert_equals "true" "$GH_LAST_WAS_NETWORK_ERROR" "Network error flag set on network error"

    rm -f "$fake_cmd"
}

test_with_detection_no_flags_on_success() {
    GH_LAST_WAS_RATE_LIMIT=true
    GH_LAST_WAS_NETWORK_ERROR=true

    gh_with_network_detection true > /dev/null 2>&1

    assert_equals "false" "$GH_LAST_WAS_RATE_LIMIT" "Rate limit flag cleared on success"
    assert_equals "false" "$GH_LAST_WAS_NETWORK_ERROR" "Network error flag cleared on success"
}

# =============================================================================
# Run tests
# =============================================================================

echo "=== GitHub Rate Limit Detection Tests ==="
run_test test_rate_limit_detects_primary_rate_limit
run_test test_rate_limit_detects_secondary_rate_limit
run_test test_rate_limit_detects_http_429
run_test test_rate_limit_detects_abuse
run_test test_rate_limit_rejects_non_rate_limit
run_test test_network_error_includes_rate_limits
run_test test_format_error_rate_limit
run_test test_format_error_network_not_rate_limit
run_test test_global_rate_limit_flag_initialized
run_test test_with_detection_sets_rate_limit_flag
run_test test_with_detection_no_rate_limit_on_network_error
run_test test_with_detection_no_flags_on_success

print_test_summary
exit_with_test_result
