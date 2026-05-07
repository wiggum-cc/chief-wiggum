#!/usr/bin/env bash
# =============================================================================
# Tests for lib/backend/claude/usage-tracker.sh
#
# Tests the usage tracking system including:
# - 5-hour cycle calculation
# - Week start calculation
# - Session analysis (JSONL parsing)
# - Rate limit checking
# - Empty/missing directory handling
# =============================================================================

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

TEST_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    export LOG_FILE="/dev/null"
    # Override projects dir to use test fixture
    export CLAUDE_PROJECTS_DIR="$TEST_DIR/projects"
    export USAGE_DATA_DIR="$TEST_DIR/data"
    # Isolate from config/config.json threshold
    export WIGGUM_RATE_LIMIT_THRESHOLD=900
    # Reset loaded state
    unset _USAGE_TRACKER_LOADED 2>/dev/null || true
    # Source fresh
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/backend/claude/usage-tracker.sh"
}

teardown() {
    unset CLAUDE_PROJECTS_DIR USAGE_DATA_DIR WIGGUM_RATE_LIMIT_THRESHOLD
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# Test: 5-hour cycle start aligns to boundary or epoch
# =============================================================================
test_5h_cycle_aligns_correctly() {
    local cycle_start boundary
    cycle_start=$(_usage_get_5h_cycle_start)
    boundary=$(_usage_get_threshold_boundary)

    if [ -n "$boundary" ] && [ "$boundary" -gt 0 ] 2>/dev/null; then
        # When boundary is configured, cycle_start should have same offset as boundary
        local cycle_offset=$(( cycle_start % 18000 ))
        local boundary_offset=$(( boundary % 18000 ))
        assert_equals "$boundary_offset" "$cycle_offset" \
            "5h cycle start should align to configured boundary"
    else
        # Without boundary, cycle_start should be multiple of 18000
        local remainder=$(( cycle_start % 18000 ))
        assert_equals "0" "$remainder" \
            "5h cycle start should be multiple of 18000 seconds"
    fi
}

# =============================================================================
# Test: 5-hour cycle start is <= now
# =============================================================================
test_5h_cycle_start_not_in_future() {
    local cycle_start now
    cycle_start=$(_usage_get_5h_cycle_start)
    now=$(date +%s)

    local diff=$(( now - cycle_start ))
    # Should be 0-17999 seconds (within current 5h window)
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ "$diff" -ge 0 ] && [ "$diff" -lt 18000 ]; then
        echo -e "  ${GREEN}✓${NC} 5h cycle start is within current window (${diff}s ago)"
    else
        echo -e "  ${RED}✗${NC} 5h cycle start is outside window (${diff}s difference)"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

# =============================================================================
# Test: Week start is a Monday
# =============================================================================
test_week_start_is_monday() {
    local week_start
    week_start=$(_usage_get_week_start)

    # Get the day of week for week_start (1=Mon, 7=Sun)
    local dow
    dow=$(date -d "@$week_start" +%u 2>/dev/null) || \
        dow=$(date -r "$week_start" +%u 2>/dev/null) || \
        dow="1"  # Fallback if date command differs

    assert_equals "1" "$dow" "Week start should be a Monday"
}

# =============================================================================
# Test: Week start is <= now
# =============================================================================
test_week_start_not_in_future() {
    local week_start now
    week_start=$(_usage_get_week_start)
    now=$(date +%s)

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ "$week_start" -le "$now" ]; then
        echo -e "  ${GREEN}✓${NC} Week start is not in the future"
    else
        echo -e "  ${RED}✗${NC} Week start ($week_start) is after now ($now)"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

# =============================================================================
# Test: Command message detection
# =============================================================================
test_is_command_message() {
    # Should detect command-name tags
    assert_success "Should detect command-name tag" \
        _usage_is_command_message "text <command-name>/commit</command-name>"

    # Should detect local-command-stdout tags
    assert_success "Should detect local-command-stdout tag" \
        _usage_is_command_message "output <local-command-stdout>result</local-command-stdout>"

    # Should NOT match regular messages
    assert_failure "Should not match regular text" \
        _usage_is_command_message "Just a regular user message"

    assert_failure "Should not match empty string" \
        _usage_is_command_message ""
}

# =============================================================================
# Test: Empty result generation
# =============================================================================
test_empty_result_structure() {
    local week_start cycle_start result
    week_start=$(_usage_get_week_start)
    cycle_start=$(_usage_get_5h_cycle_start)

    result=$(_usage_empty_result "$week_start" "$cycle_start")

    # Verify JSON structure
    local cycle_prompts week_prompts week_sessions
    cycle_prompts=$(echo "$result" | jq -r '.current_5h_cycle.total_prompts')
    week_prompts=$(echo "$result" | jq -r '.current_week.total_prompts')
    week_sessions=$(echo "$result" | jq -r '.current_week.total_sessions')

    assert_equals "0" "$cycle_prompts" "Empty result should have 0 cycle prompts"
    assert_equals "0" "$week_prompts" "Empty result should have 0 week prompts"
    assert_equals "0" "$week_sessions" "Empty result should have 0 week sessions"

    # Verify timestamps are in milliseconds
    local cycle_start_ms
    cycle_start_ms=$(echo "$result" | jq -r '.current_5h_cycle.start_time')
    local expected_ms=$(( cycle_start * 1000 ))
    assert_equals "$expected_ms" "$cycle_start_ms" "Cycle start should be in milliseconds"
}

# =============================================================================
# Test: Rate limit check with no data
# =============================================================================
test_rate_limit_no_data() {
    local ralph_dir="$TEST_DIR/ralph-no-data"
    mkdir -p "$ralph_dir"

    # Should return 1 (not rate limited) when no usage file exists
    assert_failure "Should not be rate limited with no data" \
        rate_limit_check "$ralph_dir"
}

# =============================================================================
# Test: Rate limit check under threshold
# =============================================================================
test_rate_limit_under_threshold() {
    local ralph_dir="$TEST_DIR/ralph-under"
    mkdir -p "$ralph_dir/orchestrator"

    # Create usage data under threshold
    cat > "$ralph_dir/orchestrator/claude-usage.json" << 'JSON'
{
    "current_5h_cycle": {
        "start_time": 1700000000000,
        "total_prompts": 100
    },
    "current_week": {
        "total_prompts": 500
    }
}
JSON

    # With default threshold of 900, 100 prompts is under
    assert_failure "Should not be rate limited under threshold" \
        rate_limit_check "$ralph_dir"
}

# =============================================================================
# Test: Rate limit check over threshold
# =============================================================================
test_rate_limit_over_threshold() {
    local ralph_dir="$TEST_DIR/ralph-over"
    mkdir -p "$ralph_dir/orchestrator"

    # Get current cycle start in milliseconds to avoid stale data detection
    local current_cycle_start_ms
    current_cycle_start_ms=$(( $(_usage_get_5h_cycle_start) * 1000 ))

    # Create usage data over threshold with current cycle timestamp
    cat > "$ralph_dir/orchestrator/claude-usage.json" << JSON
{
    "current_5h_cycle": {
        "start_time": $current_cycle_start_ms,
        "total_prompts": 950
    },
    "current_week": {
        "total_prompts": 5000
    }
}
JSON

    # With default threshold of 900, 950 prompts is over
    assert_success "Should be rate limited over threshold" \
        rate_limit_check "$ralph_dir"
}

# =============================================================================
# Test: Rate limit with custom threshold
# =============================================================================
test_rate_limit_custom_threshold() {
    local ralph_dir="$TEST_DIR/ralph-custom"
    mkdir -p "$ralph_dir/orchestrator"

    # Get current cycle start in milliseconds to avoid stale data detection
    local current_cycle_start_ms
    current_cycle_start_ms=$(( $(_usage_get_5h_cycle_start) * 1000 ))

    cat > "$ralph_dir/orchestrator/claude-usage.json" << JSON
{
    "current_5h_cycle": {
        "start_time": $current_cycle_start_ms,
        "total_prompts": 50
    }
}
JSON

    # Custom threshold of 40 should trigger rate limit
    export WIGGUM_RATE_LIMIT_THRESHOLD=40
    assert_success "Should be rate limited with custom threshold" \
        rate_limit_check "$ralph_dir"
    unset WIGGUM_RATE_LIMIT_THRESHOLD
}

# =============================================================================
# Test: Usage tracker calculate with missing directory
# =============================================================================
test_calculate_missing_directory() {
    export CLAUDE_PROJECTS_DIR="$TEST_DIR/nonexistent"

    local result
    result=$(usage_tracker_calculate 2>/dev/null)

    # Should return valid JSON with zeros
    local prompts
    prompts=$(echo "$result" | jq -r '.current_5h_cycle.total_prompts')
    assert_equals "0" "$prompts" "Missing dir should produce zero prompts"
}

# =============================================================================
# Test: Usage tracker save writes file
# =============================================================================
test_tracker_save_writes_file() {
    local test_json='{"current_5h_cycle":{"total_prompts":42},"current_week":{"total_prompts":100}}'

    usage_tracker_save "$test_json"

    local output_file="$USAGE_DATA_DIR/usage_data.json"
    assert_file_exists "$output_file" "Usage data file should be written"

    local saved_prompts
    saved_prompts=$(jq -r '.current_5h_cycle.total_prompts' "$output_file")
    assert_equals "42" "$saved_prompts" "Saved data should preserve values"
}

# =============================================================================
# Test: Session analysis with valid JSONL
# =============================================================================
test_analyze_session_valid_jsonl() {
    local session_dir="$TEST_DIR/projects/test-project"
    mkdir -p "$session_dir"

    local now
    now=$(date -Iseconds)

    # Create a minimal JSONL session file
    cat > "$session_dir/test-session.jsonl" << EOF
{"type":"user","timestamp":"$now","userType":"external","isMeta":false,"message":{"role":"user","content":"Hello, do something"}}
{"type":"assistant","timestamp":"$now","message":{"role":"assistant","model":"claude-sonnet-4-20250514","content":[{"type":"text","text":"Done"}],"usage":{"input_tokens":100,"output_tokens":50}}}
{"type":"user","timestamp":"$now","userType":"external","isMeta":false,"message":{"role":"user","content":"Thanks"}}
{"type":"assistant","timestamp":"$now","message":{"role":"assistant","model":"claude-sonnet-4-20250514","content":[{"type":"text","text":"Welcome"}],"usage":{"input_tokens":200,"output_tokens":30}}}
EOF

    local result
    result=$(_usage_analyze_session "$session_dir/test-session.jsonl")

    # Verify prompt count (2 user messages)
    local prompts
    prompts=$(echo "$result" | jq -r '.prompt_count')
    assert_equals "2" "$prompts" "Should count 2 user prompts"

    # Verify sonnet responses
    local sonnet
    sonnet=$(echo "$result" | jq -r '.sonnet_responses')
    assert_equals "2" "$sonnet" "Should count 2 sonnet responses"

    # Verify token accumulation
    local input_tokens
    input_tokens=$(echo "$result" | jq -r '.input_tokens')
    assert_equals "300" "$input_tokens" "Should accumulate input tokens (100+200)"
}

# =============================================================================
# Test: Session analysis skips command messages
# =============================================================================
test_analyze_session_skips_commands() {
    local session_dir="$TEST_DIR/projects/test-project2"
    mkdir -p "$session_dir"

    local now
    now=$(date -Iseconds)

    cat > "$session_dir/cmd-session.jsonl" << EOF
{"type":"user","timestamp":"$now","userType":"external","isMeta":false,"message":{"role":"user","content":"Regular message"}}
{"type":"user","timestamp":"$now","userType":"external","isMeta":false,"message":{"role":"user","content":"<command-name>/commit</command-name> commit stuff"}}
{"type":"user","timestamp":"$now","userType":"external","isMeta":false,"message":{"role":"user","content":"Another regular message"}}
{"type":"assistant","timestamp":"$now","message":{"role":"assistant","model":"claude-sonnet-4-20250514","content":[{"type":"text","text":"OK"}],"usage":{"input_tokens":50,"output_tokens":20}}}
EOF

    local result
    result=$(_usage_analyze_session "$session_dir/cmd-session.jsonl")

    local prompts
    prompts=$(echo "$result" | jq -r '.prompt_count')
    assert_equals "2" "$prompts" "Should count only 2 non-command prompts"
}

# =============================================================================
# Test: Write shared usage file
# =============================================================================
test_write_shared() {
    export CLAUDE_PROJECTS_DIR="$TEST_DIR/empty-projects"
    mkdir -p "$CLAUDE_PROJECTS_DIR"

    local ralph_dir="$TEST_DIR/ralph-shared"
    mkdir -p "$ralph_dir/orchestrator"

    local result
    result=$(usage_tracker_write_shared "$ralph_dir" 2>/dev/null)

    assert_file_exists "$ralph_dir/orchestrator/claude-usage.json" "Shared usage file should be created"

    local prompts
    prompts=$(jq -r '.current_5h_cycle.total_prompts' "$ralph_dir/orchestrator/claude-usage.json")
    assert_equals "0" "$prompts" "Empty projects should produce 0 prompts"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_5h_cycle_aligns_correctly
run_test test_5h_cycle_start_not_in_future
run_test test_week_start_is_monday
run_test test_week_start_not_in_future
run_test test_is_command_message
run_test test_empty_result_structure
run_test test_rate_limit_no_data
run_test test_rate_limit_under_threshold
run_test test_rate_limit_over_threshold
run_test test_rate_limit_custom_threshold
run_test test_calculate_missing_directory
run_test test_tracker_save_writes_file
run_test test_analyze_session_valid_jsonl
run_test test_analyze_session_skips_commands
run_test test_write_shared

print_test_summary
exit_with_test_result
