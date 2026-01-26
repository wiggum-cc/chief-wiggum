#!/usr/bin/env bash
# Test suite for security-fix agent
# Tests: markdown agent loading, step-config handling

set -euo pipefail

# Get the script directory and project root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Source the test framework
source "$SCRIPT_DIR/test-framework.sh"

# Setup WIGGUM_HOME for tests
export WIGGUM_HOME="$PROJECT_ROOT"

# Temporary directory for test files
TEST_TMP_DIR=""

# =============================================================================
# Setup and Teardown
# =============================================================================

setup() {
    TEST_TMP_DIR=$(mktemp -d)
    mkdir -p "$TEST_TMP_DIR/reports"
}

teardown() {
    if [ -n "$TEST_TMP_DIR" ] && [ -d "$TEST_TMP_DIR" ]; then
        rm -rf "$TEST_TMP_DIR"
    fi
}

# =============================================================================
# Test: Markdown Agent Definition
# =============================================================================

test_security_fix_md_exists() {
    assert_file_exists "$WIGGUM_HOME/lib/agents/engineering/security-fix.md" \
        "security-fix.md agent definition should exist"
}

test_security_fix_md_has_required_frontmatter() {
    local md_file="$WIGGUM_HOME/lib/agents/engineering/security-fix.md"

    # Check for required frontmatter fields
    assert_file_contains "$md_file" "type: engineering.security-fix" \
        "Should have type field"
    assert_file_contains "$md_file" "valid_results:" \
        "Should have valid_results field"
    assert_file_contains "$md_file" "mode: ralph_loop" \
        "Should have mode field"
}

test_security_fix_md_has_prompt_sections() {
    local md_file="$WIGGUM_HOME/lib/agents/engineering/security-fix.md"

    assert_file_contains "$md_file" "<WIGGUM_SYSTEM_PROMPT>" \
        "Should have system prompt section"
    assert_file_contains "$md_file" "<WIGGUM_USER_PROMPT>" \
        "Should have user prompt section"
    assert_file_contains "$md_file" "{{context_section}}" \
        "Should use context_section for parent report"
}

# =============================================================================
# Test: Step-based report lookup
# =============================================================================

test_agent_find_latest_report_by_step_id() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    # Create a report file named by step ID
    cat > "$TEST_TMP_DIR/reports/1234567890-audit-report.md" << 'EOF'
# Report content
EOF

    local result
    result=$(agent_find_latest_report "$TEST_TMP_DIR" "audit")

    assert_not_equals "" "$result" "Should find report by step ID"
    assert_file_exists "$result" "Report file should exist"
}

test_agent_find_latest_report_not_found_by_agent_type() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    # Create a report file named by step ID
    cat > "$TEST_TMP_DIR/reports/1234567890-audit-report.md" << 'EOF'
# Report content
EOF

    # Try to find by agent type (should fail - files named by step ID)
    local result
    result=$(agent_find_latest_report "$TEST_TMP_DIR" "security-audit")

    assert_equals "" "$result" "Should NOT find report by agent type when file named by step ID"
}

# =============================================================================
# Run Tests
# =============================================================================

# Markdown agent definition
run_test test_security_fix_md_exists
run_test test_security_fix_md_has_required_frontmatter
run_test test_security_fix_md_has_prompt_sections

# Step-based report lookup
run_test test_agent_find_latest_report_by_step_id
run_test test_agent_find_latest_report_not_found_by_agent_type

# Print summary
print_test_summary
exit_with_test_result
