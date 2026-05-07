#!/usr/bin/env bash
# Test suite for engineering.intent-distill agent
# Tests: completion check, gate result determination, graceful degradation

set -euo pipefail

# Get the script directory and project root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Source the test framework
source "$SCRIPT_DIR/test-framework.sh"

# Setup WIGGUM_HOME for tests
export WIGGUM_HOME="$PROJECT_ROOT"

# Test temp directory
TEST_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    mkdir -p "$TEST_DIR/reports"
    mkdir -p "$TEST_DIR/workspace"
    mkdir -p "$TEST_DIR/results"
    mkdir -p "$TEST_DIR/logs"
    mkdir -p "$TEST_DIR/summaries"

    # Reset module state so agent can be re-sourced
    unset _INTENT_AVAILABLE _INTENT_AVAILABLE_BIN 2>/dev/null || true

    # Default: intent CLI not available (override in specific tests)
    export WIGGUM_INTENT_BIN="/nonexistent/intent-bin"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
    unset WIGGUM_INTENT_BIN 2>/dev/null || true
    unset _INTENT_AVAILABLE _INTENT_AVAILABLE_BIN 2>/dev/null || true
}

# =============================================================================
# Helpers
# =============================================================================

# Source the agent in a subshell to get access to its functions
# We source agent-base first (needed by the agent), then the agent itself
_source_agent() {
    # Source agent-base which loads platform, logger, etc.
    source "$WIGGUM_HOME/lib/core/agent-base.sh"
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/defaults.sh"
    # Source the agent (will re-init metadata, which is fine)
    source "$WIGGUM_HOME/lib/agents/engineering/intent-distill.sh"
}

# =============================================================================
# Test: Bash syntax validation
# =============================================================================

test_intent_distill_syntax() {
    if bash -n "$WIGGUM_HOME/lib/agents/engineering/intent-distill.sh" 2>/dev/null; then
        assert_success "intent-distill.sh should have valid bash syntax" true
    else
        assert_failure "intent-distill.sh should have valid bash syntax" true
    fi
}

# =============================================================================
# Test: Agent metadata
# =============================================================================

test_agent_metadata_set() {
    (
        _source_agent
        assert_equals "engineering.intent-distill" "$AGENT_TYPE" "AGENT_TYPE should be set"
        assert_not_empty "$AGENT_DESCRIPTION" "AGENT_DESCRIPTION should not be empty"
    )
}

# =============================================================================
# Test: Completion check - missing spec file
# =============================================================================

test_completion_check_missing_spec() {
    (
        _source_agent
        _DISTILL_SPEC_FILE="$TEST_DIR/reports/distilled.intent"

        # No spec file exists - should return 1 (not complete)
        local result=0
        _distill_completion_check || result=$?
        assert_equals "1" "$result" "Missing spec should return 1 (not complete)"
    )
}

# =============================================================================
# Test: Completion check - empty spec file
# =============================================================================

test_completion_check_empty_spec() {
    (
        _source_agent
        _DISTILL_SPEC_FILE="$TEST_DIR/reports/distilled.intent"

        # Create empty spec file
        touch "$TEST_DIR/reports/distilled.intent"

        local result=0
        _distill_completion_check || result=$?
        assert_equals "1" "$result" "Empty spec should return 1 (not complete)"
    )
}

# =============================================================================
# Test: Completion check - valid spec with distilled keyword, no intent CLI
# =============================================================================

test_completion_check_fallback_with_keyword() {
    (
        _source_agent
        export WIGGUM_INTENT_BIN="/nonexistent/intent-bin"
        _INTENT_AVAILABLE=""
        _INTENT_AVAILABLE_BIN=""
        _DISTILL_SPEC_FILE="$TEST_DIR/reports/distilled.intent"

        # Create spec file with distilled keyword
        cat > "$TEST_DIR/reports/distilled.intent" << 'SPEC'
distilled pattern TestPattern {
    source: "src/**/*.rs"
    confidence: 0.8
    observation { "Test pattern" }
}
SPEC

        local result=0
        _distill_completion_check || result=$?
        assert_equals "0" "$result" "Spec with 'distilled' keyword should pass fallback check"
    )
}

# =============================================================================
# Test: Completion check - spec without distilled keyword, no intent CLI
# =============================================================================

test_completion_check_fallback_without_keyword() {
    (
        _source_agent
        export WIGGUM_INTENT_BIN="/nonexistent/intent-bin"
        _INTENT_AVAILABLE=""
        _INTENT_AVAILABLE_BIN=""
        _DISTILL_SPEC_FILE="$TEST_DIR/reports/distilled.intent"

        # Create spec file without distilled keyword
        echo "some random content without the keyword" > "$TEST_DIR/reports/distilled.intent"

        local result=0
        _distill_completion_check || result=$?
        assert_equals "1" "$result" "Spec without 'distilled' keyword should fail fallback check"
    )
}

# =============================================================================
# Test: Completion check - spec with lint pass (intent CLI available)
# =============================================================================

test_completion_check_lint_pass() {
    (
        _source_agent

        # Create a mock intent binary that succeeds
        local mock_bin="$TEST_DIR/mock-intent"
        cat > "$mock_bin" << 'MOCKEOF'
#!/usr/bin/env bash
# Mock intent CLI that always passes lint
echo "Lint passed: 0 errors, 0 warnings"
exit 0
MOCKEOF
        chmod +x "$mock_bin"
        export WIGGUM_INTENT_BIN="$mock_bin"
        _INTENT_AVAILABLE=""
        _INTENT_AVAILABLE_BIN=""
        _DISTILL_SPEC_FILE="$TEST_DIR/reports/distilled.intent"

        # Create spec file
        echo "distilled pattern Foo { source: \"x\" }" > "$TEST_DIR/reports/distilled.intent"

        local result=0
        _distill_completion_check || result=$?
        assert_equals "0" "$result" "Spec passing lint should return 0 (complete)"
    )
}

# =============================================================================
# Test: Completion check - spec with lint errors (intent CLI available)
# =============================================================================

test_completion_check_lint_fail() {
    (
        _source_agent

        # Create a mock intent binary that fails lint
        local mock_bin="$TEST_DIR/mock-intent"
        cat > "$mock_bin" << 'MOCKEOF'
#!/usr/bin/env bash
# Mock intent CLI that fails lint
echo "Error: missing required field 'confidence' at line 2"
exit 1
MOCKEOF
        chmod +x "$mock_bin"
        export WIGGUM_INTENT_BIN="$mock_bin"
        _INTENT_AVAILABLE=""
        _INTENT_AVAILABLE_BIN=""
        _DISTILL_SPEC_FILE="$TEST_DIR/reports/distilled.intent"

        # Create spec file
        echo "distilled pattern Foo { source: \"x\" }" > "$TEST_DIR/reports/distilled.intent"

        local result=0
        _distill_completion_check || result=$?
        assert_equals "1" "$result" "Spec failing lint should return 1 (not complete)"
    )
}

# =============================================================================
# Test: Intent CLI check - available
# =============================================================================

test_intent_cli_check_available() {
    (
        _source_agent

        # Create a mock intent binary
        local mock_bin="$TEST_DIR/mock-intent"
        echo '#!/usr/bin/env bash' > "$mock_bin"
        echo 'echo "intent v0.1.0"' >> "$mock_bin"
        chmod +x "$mock_bin"
        export WIGGUM_INTENT_BIN="$mock_bin"
        _INTENT_AVAILABLE=""
        _INTENT_AVAILABLE_BIN=""

        local result=0
        _check_intent_cli || result=$?
        assert_equals "0" "$result" "Mock intent CLI should be detected as available"
    )
}

# =============================================================================
# Test: Intent CLI check - unavailable
# =============================================================================

test_intent_cli_check_unavailable() {
    (
        _source_agent
        export WIGGUM_INTENT_BIN="/nonexistent/intent-bin"
        _INTENT_AVAILABLE=""
        _INTENT_AVAILABLE_BIN=""

        local result=0
        _check_intent_cli || result=$?
        assert_equals "1" "$result" "Nonexistent intent CLI should be detected as unavailable"
    )
}

# =============================================================================
# Test: User prompt - iteration 0 is structural
# =============================================================================

test_user_prompt_iteration_0() {
    (
        _source_agent
        _DISTILL_SPEC_FILE="$TEST_DIR/reports/distilled.intent"
        _DISTILL_WORKSPACE="$TEST_DIR/workspace"
        export RALPH_RUN_ID=""

        local output
        output=$(_distill_user_prompt 0 "$TEST_DIR" "" "")

        assert_output_contains "$output" "STRUCTURAL EXTRACTION" "Iteration 0 should be structural phase"
        assert_output_contains "$output" "Directory structure" "Should mention directory scanning"
        assert_output_not_contains "$output" "BEHAVIORAL EXTRACTION" "Iteration 0 should NOT be behavioral phase"
    )
}

# =============================================================================
# Test: User prompt - iteration 1+ is behavioral
# =============================================================================

test_user_prompt_iteration_1() {
    (
        _source_agent
        _DISTILL_SPEC_FILE="$TEST_DIR/reports/distilled.intent"
        _DISTILL_WORKSPACE="$TEST_DIR/workspace"
        export WIGGUM_INTENT_BIN="/nonexistent/intent-bin"
        _INTENT_AVAILABLE=""
        _INTENT_AVAILABLE_BIN=""
        export RALPH_RUN_ID=""

        local output
        output=$(_distill_user_prompt 1 "$TEST_DIR" "" "")

        assert_output_contains "$output" "BEHAVIORAL EXTRACTION" "Iteration 1 should be behavioral phase"
        assert_output_not_contains "$output" "STRUCTURAL EXTRACTION" "Iteration 1 should NOT be structural phase"
    )
}

# =============================================================================
# Test: User prompt - lint errors injected when spec exists and CLI available
# =============================================================================

test_user_prompt_lint_errors_injected() {
    (
        _source_agent

        # Create a mock intent binary that fails
        local mock_bin="$TEST_DIR/mock-intent"
        cat > "$mock_bin" << 'MOCKEOF'
#!/usr/bin/env bash
echo "Error: missing field 'confidence' at line 3"
exit 1
MOCKEOF
        chmod +x "$mock_bin"
        export WIGGUM_INTENT_BIN="$mock_bin"
        _INTENT_AVAILABLE=""
        _INTENT_AVAILABLE_BIN=""
        _DISTILL_SPEC_FILE="$TEST_DIR/reports/distilled.intent"
        _DISTILL_WORKSPACE="$TEST_DIR/workspace"
        export RALPH_RUN_ID=""

        # Create spec file
        echo "distilled pattern Foo {}" > "$TEST_DIR/reports/distilled.intent"

        local output
        output=$(_distill_user_prompt 2 "$TEST_DIR" "" "")

        assert_output_contains "$output" "Lint Errors" "Should include lint error section"
        assert_output_contains "$output" "missing field" "Should include actual lint error text"
    )
}

# =============================================================================
# Test: System prompt contains DSL reference
# =============================================================================

test_system_prompt_contains_dsl_reference() {
    (
        _source_agent
        _AGENT_PROJECT_DIR="$TEST_DIR"

        local output
        output=$(_get_system_prompt "$TEST_DIR/workspace")

        assert_output_contains "$output" "distilled pattern" "System prompt should reference distilled pattern"
        assert_output_contains "$output" "distilled constraint" "System prompt should reference distilled constraint"
        assert_output_contains "$output" "confidence" "System prompt should mention confidence"
        assert_output_contains "$output" "observation" "System prompt should mention observation"
        assert_output_contains "$output" "RetryWithBackoff" "System prompt should include RetryWithBackoff example"
        assert_output_contains "$output" "ObservedLayering" "System prompt should include ObservedLayering example"
    )
}

# =============================================================================
# Test: agents.json has intent-distill entry
# =============================================================================

test_agents_json_has_entry() {
    local entry
    entry=$(jq '.agents["engineering.intent-distill"]' "$WIGGUM_HOME/config/agents.json" 2>/dev/null)
    assert_not_equals "null" "$entry" "agents.json should have engineering.intent-distill entry"

    local max_iter
    max_iter=$(jq '.agents["engineering.intent-distill"].max_iterations' "$WIGGUM_HOME/config/agents.json" 2>/dev/null)
    assert_equals "8" "$max_iter" "max_iterations should be 8"

    local max_turns
    max_turns=$(jq '.agents["engineering.intent-distill"].max_turns' "$WIGGUM_HOME/config/agents.json" 2>/dev/null)
    assert_equals "80" "$max_turns" "max_turns should be 80"

    local fix_jump
    fix_jump=$(jq -r '.agents["engineering.intent-distill"].result_mappings.FIX.default_jump' "$WIGGUM_HOME/config/agents.json" 2>/dev/null)
    assert_equals "self" "$fix_jump" "FIX default_jump should be 'self'"
}

# =============================================================================
# Test: agents.json remains valid JSON after edit
# =============================================================================

test_agents_json_valid() {
    if jq '.' "$WIGGUM_HOME/config/agents.json" > /dev/null 2>&1; then
        assert_success "config/agents.json should be valid JSON" true
    else
        assert_failure "config/agents.json is invalid JSON" false
    fi
}

# =============================================================================
# Test: pipeline JSON is valid and correctly structured
# =============================================================================

test_pipeline_json_valid() {
    local pipeline_file="$WIGGUM_HOME/config/pipelines/intent-distill.json"

    assert_file_exists "$pipeline_file" "Pipeline file should exist"

    if jq '.' "$pipeline_file" > /dev/null 2>&1; then
        assert_success "Pipeline JSON should be valid" true
    else
        assert_failure "Pipeline JSON is invalid" false
    fi

    local name
    name=$(jq -r '.name' "$pipeline_file" 2>/dev/null)
    assert_equals "intent-distill" "$name" "Pipeline name should be 'intent-distill'"

    local agent
    agent=$(jq -r '.steps[0].agent' "$pipeline_file" 2>/dev/null)
    assert_equals "engineering.intent-distill" "$agent" "Step agent should be engineering.intent-distill"

    local readonly_val
    readonly_val=$(jq '.steps[0].readonly' "$pipeline_file" 2>/dev/null)
    assert_equals "true" "$readonly_val" "Step should be readonly"

    local max_val
    max_val=$(jq '.steps[0].max' "$pipeline_file" 2>/dev/null)
    assert_equals "2" "$max_val" "Step max should be 2"
}

# =============================================================================
# Test: Graceful degradation with nonexistent WIGGUM_INTENT_BIN
# =============================================================================

test_graceful_degradation() {
    (
        _source_agent
        export WIGGUM_INTENT_BIN="/definitely/not/a/real/binary"
        _INTENT_AVAILABLE=""
        _INTENT_AVAILABLE_BIN=""

        # Should not fail, just return 1 (not available)
        local result=0
        _check_intent_cli || result=$?
        assert_equals "1" "$result" "Should gracefully handle missing intent CLI"

        # After check, _INTENT_AVAILABLE should be cached as "0"
        assert_equals "0" "$_INTENT_AVAILABLE" "Should cache unavailable status"

        # Second call should use cache and also return 1
        local result2=0
        _check_intent_cli || result2=$?
        assert_equals "1" "$result2" "Cached check should also return unavailable"
    )
}

# =============================================================================
# Test: agent_valid_results returns correct values
# =============================================================================

test_valid_results() {
    (
        _source_agent
        local results
        results=$(agent_valid_results)
        assert_equals "PASS|FAIL|FIX" "$results" "Valid results should be PASS|FAIL|FIX"
    )
}

# =============================================================================
# Test: agent_required_paths returns workspace
# =============================================================================

test_required_paths() {
    (
        _source_agent
        local paths
        paths=$(agent_required_paths)
        assert_equals "workspace" "$paths" "Required paths should include workspace"
    )
}

# =============================================================================
# Run all tests
# =============================================================================

run_test test_intent_distill_syntax
run_test test_agent_metadata_set
run_test test_completion_check_missing_spec
run_test test_completion_check_empty_spec
run_test test_completion_check_fallback_with_keyword
run_test test_completion_check_fallback_without_keyword
run_test test_completion_check_lint_pass
run_test test_completion_check_lint_fail
run_test test_intent_cli_check_available
run_test test_intent_cli_check_unavailable
run_test test_user_prompt_iteration_0
run_test test_user_prompt_iteration_1
run_test test_user_prompt_lint_errors_injected
run_test test_system_prompt_contains_dsl_reference
run_test test_agents_json_has_entry
run_test test_agents_json_valid
run_test test_pipeline_json_valid
run_test test_graceful_degradation
run_test test_valid_results
run_test test_required_paths

# Print summary and exit
print_test_summary
exit_with_test_result
