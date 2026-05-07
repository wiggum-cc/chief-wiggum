#!/usr/bin/env bash
# test_mock_claude.sh - Tests for the mock Claude CLI
#
# Validates all mock-claude.sh features including:
# - Basic backward-compatible behavior
# - Scenario-based responses
# - Session tracking
# - Max-turns simulation
# - Signal exit codes
# - File side-effects
# - Argument validation
# - Response sequencing
# - Delay jitter

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$TESTS_DIR/test-framework.sh"
source "$TESTS_DIR/mocks/mock-helpers.sh"

# =============================================================================
# Setup / Teardown
# =============================================================================

setup() {
    mock_setup
}

teardown() {
    mock_teardown
}

# =============================================================================
# 1. Backward Compatibility Tests
# =============================================================================

test_basic_text_output() {
    export MOCK_CLAUDE_RESPONSE="Hello from mock"
    local output
    output=$("$CLAUDE" -p "test")
    assert_equals "Hello from mock" "$output" "Should return configured response"
}

test_default_response() {
    local output
    output=$("$CLAUDE" -p "test")
    assert_equals "Task completed successfully." "$output" "Should return default response"
}

test_version_flag() {
    local output
    output=$("$CLAUDE" --version)
    assert_output_contains "$output" "mock" "Version should mention mock"
}

test_exit_code() {
    export MOCK_CLAUDE_EXIT_CODE=42
    local exit_code=0
    "$CLAUDE" -p "test" || exit_code=$?
    assert_equals "42" "$exit_code" "Should return configured exit code"
}

test_fail_after_n() {
    export MOCK_CLAUDE_FAIL_AFTER=2
    local exit_code=0

    "$CLAUDE" -p "first" || exit_code=$?
    assert_equals "0" "$exit_code" "First invocation should succeed"

    exit_code=0
    "$CLAUDE" -p "second" 2>/dev/null || exit_code=$?
    assert_not_equals "0" "$exit_code" "Second invocation should fail"
}

test_simple_stream_json() {
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_valid_stream_json "$output"
    assert_output_contains "$output" "session_start" "Should have session_start"
    assert_output_contains "$output" "result" "Should have result"
}

# =============================================================================
# 2. Scenario Tests
# =============================================================================

test_scenario_simple() {
    export MOCK_CLAUDE_SCENARIO="simple"
    export MOCK_CLAUDE_RESPONSE="Simple response"
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_valid_stream_json "$output"
    assert_mock_output_assistant_count "$output" 1
    assert_output_contains "$output" "Simple response" "Should contain response text"
}

test_scenario_multi_turn() {
    export MOCK_CLAUDE_SCENARIO="multi-turn"
    export MOCK_CLAUDE_SIMULATE_TURNS=4
    export MOCK_CLAUDE_RESPONSE="Final answer"
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_valid_stream_json "$output"
    assert_mock_output_assistant_count "$output" 4
    assert_mock_output_num_turns "$output" "4"
    assert_output_contains "$output" "Final answer" "Should contain final response"
    assert_output_contains "$output" "Working on step 1" "Should have intermediate steps"
}

test_scenario_tool_heavy() {
    export MOCK_CLAUDE_SCENARIO="tool-heavy"
    export MOCK_CLAUDE_RESPONSE="All done"
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_valid_stream_json "$output"
    assert_mock_output_has_tool_use "$output" "bash"
    assert_mock_output_has_tool_use "$output" "edit"
    assert_mock_output_has_tool_use "$output" "read"
    assert_output_contains "$output" "tool_result" "Should have tool results"
    assert_output_contains "$output" "All done" "Should contain final response"
}

test_scenario_hit_turn_limit() {
    export MOCK_CLAUDE_SCENARIO="hit-turn-limit"
    export MOCK_CLAUDE_RESPONSE="unfinished work"
    local output
    output=$("$CLAUDE" --output-format stream-json --max-turns 3 -p "test")
    assert_mock_output_valid_stream_json "$output"
    assert_mock_output_num_turns "$output" "3"
    assert_output_contains "$output" "turn limit" "Should mention turn limit"
    assert_output_contains "$output" "unfinished work" "Should contain response"
}

test_scenario_interrupted() {
    export MOCK_CLAUDE_SCENARIO="interrupted"
    export MOCK_CLAUDE_RESPONSE="Partial work"
    local output exit_code=0
    output=$("$CLAUDE" --output-format stream-json -p "test") || exit_code=$?
    assert_equals "130" "$exit_code" "Interrupted scenario should exit 130"
    assert_output_contains "$output" "is_error\":true" "Result should indicate error"
}

test_scenario_file_edit() {
    export MOCK_CLAUDE_SCENARIO="file-edit"
    export MOCK_CLAUDE_RESPONSE="Fix applied"
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_valid_stream_json "$output"
    assert_mock_output_has_tool_use "$output" "read"
    assert_mock_output_has_tool_use "$output" "edit"
    assert_mock_output_has_tool_use "$output" "write"
    assert_mock_output_num_turns "$output" "3"
}

test_scenario_resume() {
    export MOCK_CLAUDE_RESPONSE="Continued work"
    local output
    output=$("$CLAUDE" --output-format stream-json --resume "session-abc-123" -p "continue")
    assert_mock_output_valid_stream_json "$output"
    assert_output_contains "$output" "Resuming previous session" "Should indicate resume"
    assert_output_contains "$output" "session-abc-123" "Should use resume session ID"
}

# =============================================================================
# 3. Session Tracking Tests
# =============================================================================

test_session_id_from_flag() {
    export MOCK_SESSION_ID=""
    local output
    output=$("$CLAUDE" --output-format stream-json --session-id "my-session-001" -p "test")
    local session_id
    session_id=$(mock_extract_session_id_from_output "$output")
    assert_equals "my-session-001" "$session_id" "Should use --session-id value"
    assert_mock_session_tracked "my-session-001"
}

test_session_id_from_resume() {
    local output
    output=$("$CLAUDE" --output-format stream-json --resume "resume-session-002" -p "test")
    local session_id
    session_id=$(mock_extract_session_id_from_output "$output")
    assert_equals "resume-session-002" "$session_id" "Should use --resume session ID"
}

test_session_id_from_env() {
    export MOCK_SESSION_ID="env-session-003"
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    local session_id
    session_id=$(mock_extract_session_id_from_output "$output")
    assert_equals "env-session-003" "$session_id" "Should use MOCK_SESSION_ID env"
}

test_session_turn_counting() {
    export MOCK_SESSION_ID="counting-session"
    "$CLAUDE" --output-format stream-json -p "turn1" > /dev/null
    "$CLAUDE" --output-format stream-json -p "turn2" > /dev/null
    "$CLAUDE" --output-format stream-json -p "turn3" > /dev/null
    local turn_count
    turn_count=$(mock_get_session_turn_count "counting-session")
    assert_equals "3" "$turn_count" "Session should track 3 turns"
}

test_resume_priority_over_session_id() {
    # --resume should take priority over --session-id
    local output
    output=$("$CLAUDE" --output-format stream-json --session-id "new-session" --resume "old-session" -p "test")
    local session_id
    session_id=$(mock_extract_session_id_from_output "$output")
    assert_equals "old-session" "$session_id" "Resume should take priority over session-id"
}

# =============================================================================
# 4. Max-Turns Simulation Tests
# =============================================================================

test_simulate_turns_default() {
    export MOCK_CLAUDE_SIMULATE_TURNS=2
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_assistant_count "$output" 2
    assert_mock_output_num_turns "$output" "2"
}

test_simulate_turns_with_scenario() {
    export MOCK_CLAUDE_SCENARIO="multi-turn"
    export MOCK_CLAUDE_SIMULATE_TURNS=5
    export MOCK_CLAUDE_RESPONSE="done"
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_assistant_count "$output" 5
    assert_mock_output_num_turns "$output" "5"
}

# =============================================================================
# 5. Signal Exit Code Tests
# =============================================================================

test_exit_signal_sigint() {
    export MOCK_CLAUDE_EXIT_SIGNAL="sigint"
    local exit_code=0
    "$CLAUDE" -p "test" || exit_code=$?
    assert_equals "130" "$exit_code" "SIGINT should return 130"
}

test_exit_signal_sigterm() {
    export MOCK_CLAUDE_EXIT_SIGNAL="sigterm"
    local exit_code=0
    "$CLAUDE" -p "test" || exit_code=$?
    assert_equals "143" "$exit_code" "SIGTERM should return 143"
}

test_exit_signal_numeric() {
    export MOCK_CLAUDE_EXIT_SIGNAL="130"
    local exit_code=0
    "$CLAUDE" -p "test" || exit_code=$?
    assert_equals "130" "$exit_code" "Numeric signal should return same code"
}

test_exit_signal_uppercase() {
    export MOCK_CLAUDE_EXIT_SIGNAL="SIGINT"
    local exit_code=0
    "$CLAUDE" -p "test" || exit_code=$?
    assert_equals "130" "$exit_code" "Uppercase SIGINT should return 130"
}

test_exit_signal_overrides_exit_code() {
    export MOCK_CLAUDE_EXIT_CODE=0
    export MOCK_CLAUDE_EXIT_SIGNAL="sigterm"
    local exit_code=0
    "$CLAUDE" -p "test" || exit_code=$?
    assert_equals "143" "$exit_code" "Signal should override exit code"
}

# =============================================================================
# 6. File Side-Effects Tests
# =============================================================================

test_touch_single_file() {
    local target_file="$MOCK_DIR/touched-file.txt"
    export MOCK_CLAUDE_TOUCH_FILES="$target_file"
    "$CLAUDE" -p "test" > /dev/null
    assert_file_exists "$target_file" "Should create touched file"
}

test_touch_multiple_files() {
    local file1="$MOCK_DIR/file1.txt"
    local file2="$MOCK_DIR/file2.txt"
    local file3="$MOCK_DIR/subdir/file3.txt"
    export MOCK_CLAUDE_TOUCH_FILES="$file1:$file2:$file3"
    "$CLAUDE" -p "test" > /dev/null
    assert_file_exists "$file1" "Should create file1"
    assert_file_exists "$file2" "Should create file2"
    assert_file_exists "$file3" "Should create file3 in subdirectory"
}

test_touch_modifies_existing() {
    local target_file="$MOCK_DIR/existing.txt"
    echo "original content" > "$target_file"
    export MOCK_CLAUDE_TOUCH_FILES="$target_file"
    "$CLAUDE" -p "test" > /dev/null
    assert_file_contains "$target_file" "original content" "Should keep original content"
    assert_file_contains "$target_file" "Modified by mock-claude" "Should append modification"
}

# =============================================================================
# 7. Argument Validation Tests
# =============================================================================

test_args_logged_correctly() {
    "$CLAUDE" --verbose --output-format stream-json --max-turns 5 \
        --dangerously-skip-permissions -p "hello world" > /dev/null
    assert_mock_invocation_count "1"
    assert_mock_received_arg 1 "--verbose"
    assert_mock_received_arg 1 "--output-format"
    assert_mock_received_arg 1 "stream-json"
    assert_mock_received_arg 1 "--max-turns"
    assert_mock_received_arg 1 "5"
    assert_mock_received_arg 1 "--dangerously-skip-permissions"
    assert_mock_received_arg 1 "-p"
    assert_mock_received_arg 1 "hello world"
}

test_parsed_max_turns() {
    "$CLAUDE" --output-format stream-json --max-turns 10 -p "test" > /dev/null
    assert_mock_parsed_max_turns 1 "10"
}

test_parsed_verbose() {
    "$CLAUDE" --verbose -p "test" > /dev/null
    assert_mock_parsed_verbose 1
}

test_parsed_user_prompt() {
    "$CLAUDE" -p "my test prompt" > /dev/null
    assert_mock_had_user_prompt 1
}

test_parsed_system_prompt() {
    "$CLAUDE" --append-system-prompt "system instructions" -p "test" > /dev/null
    assert_mock_had_system_prompt 1
}

test_skip_permissions_assertion() {
    "$CLAUDE" --dangerously-skip-permissions -p "test" > /dev/null
    assert_mock_received_skip_permissions 1
}

test_not_received_arg() {
    "$CLAUDE" -p "test" > /dev/null
    assert_mock_not_received_arg 1 "--resume" "Should not have --resume"
    assert_mock_not_received_arg 1 "--session-id" "Should not have --session-id"
}

# =============================================================================
# 8. Response Sequencing Tests
# =============================================================================

test_responses_file_sequential() {
    local responses_file="$MOCK_DIR/responses.txt"
    printf '%s\n' "Response one" "Response two" "Response three" > "$responses_file"
    export MOCK_CLAUDE_RESPONSES_FILE="$responses_file"

    local out1 out2 out3
    out1=$("$CLAUDE" -p "first")
    out2=$("$CLAUDE" -p "second")
    out3=$("$CLAUDE" -p "third")

    assert_equals "Response one" "$out1" "First call should get first response"
    assert_equals "Response two" "$out2" "Second call should get second response"
    assert_equals "Response three" "$out3" "Third call should get third response"
}

test_responses_file_exhausted_falls_back() {
    local responses_file="$MOCK_DIR/responses.txt"
    echo "Only response" > "$responses_file"
    export MOCK_CLAUDE_RESPONSES_FILE="$responses_file"
    export MOCK_CLAUDE_RESPONSE="Fallback response"

    local out1 out2
    out1=$("$CLAUDE" -p "first")
    out2=$("$CLAUDE" -p "second")

    assert_equals "Only response" "$out1" "First call should get file response"
    assert_equals "Fallback response" "$out2" "Second call should fall back to env var"
}

test_responses_file_with_stream_json() {
    local responses_file="$MOCK_DIR/responses.txt"
    printf '%s\n' "Stream response 1" "Stream response 2" > "$responses_file"
    export MOCK_CLAUDE_RESPONSES_FILE="$responses_file"

    local out1 out2
    out1=$("$CLAUDE" --output-format stream-json -p "first")
    out2=$("$CLAUDE" --output-format stream-json -p "second")

    assert_output_contains "$out1" "Stream response 1" "First stream should have response 1"
    assert_output_contains "$out2" "Stream response 2" "Second stream should have response 2"
}

# =============================================================================
# 9. Delay / Jitter Tests
# =============================================================================

test_fixed_delay() {
    export MOCK_CLAUDE_DELAY=1
    local start end elapsed
    start=$(date +%s)
    "$CLAUDE" -p "test" > /dev/null
    end=$(date +%s)
    elapsed=$((end - start))
    assert_greater_than "$elapsed" 0 "Should have at least 1 second delay"
}

test_delay_range_executes() {
    # Just verify it doesn't error with the range format
    export MOCK_CLAUDE_DELAY_RANGE="0.01-0.02"
    local exit_code=0
    "$CLAUDE" -p "test" > /dev/null || exit_code=$?
    assert_equals "0" "$exit_code" "Delay range should not cause errors"
}

# =============================================================================
# Tool Use Tests (MOCK_CLAUDE_TOOL_USE)
# =============================================================================

test_tool_use_single() {
    export MOCK_CLAUDE_TOOL_USE="bash"
    export MOCK_CLAUDE_RESPONSE="Done with bash"
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_valid_stream_json "$output"
    assert_mock_output_has_tool_use "$output" "bash"
    assert_output_contains "$output" "Done with bash" "Should contain response"
}

test_tool_use_multiple() {
    export MOCK_CLAUDE_TOOL_USE="bash,edit,write"
    export MOCK_CLAUDE_RESPONSE="All tools used"
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_has_tool_use "$output" "bash"
    assert_mock_output_has_tool_use "$output" "edit"
    assert_mock_output_has_tool_use "$output" "write"
    assert_mock_output_num_turns "$output" "4"
}

test_tool_use_custom() {
    export MOCK_CLAUDE_TOOL_USE="custom_tool"
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_has_tool_use "$output" "custom_tool"
}

# =============================================================================
# Cost Reporting Tests
# =============================================================================

test_default_cost() {
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_cost "$output" "0.01"
}

test_custom_cost() {
    export MOCK_CLAUDE_COST_USD="0.25"
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_cost "$output" "0.25"
}

# =============================================================================
# Integration: Combined Features
# =============================================================================

test_combined_scenario_with_touch_and_signal() {
    export MOCK_CLAUDE_SCENARIO="interrupted"
    export MOCK_CLAUDE_RESPONSE="Partial work"
    local target_file="$MOCK_DIR/partial.txt"
    export MOCK_CLAUDE_TOUCH_FILES="$target_file"

    local output exit_code=0
    output=$("$CLAUDE" --output-format stream-json -p "test") || exit_code=$?

    assert_equals "130" "$exit_code" "Should exit with 130 (interrupted)"
    assert_file_exists "$target_file" "Should create file before exiting"
    assert_output_contains "$output" "Partial work" "Should output partial response"
}

test_combined_resume_with_tool_use() {
    export MOCK_CLAUDE_TOOL_USE="bash"
    export MOCK_CLAUDE_RESPONSE="Resumed and ran tools"

    local output
    output=$("$CLAUDE" --output-format stream-json --resume "prev-session" -p "continue")

    # Resume takes precedence for scenario, but tool_use should still work when
    # no explicit scenario is set. Here resume scenario is triggered.
    assert_output_contains "$output" "prev-session" "Should use resume session"
    assert_mock_output_valid_stream_json "$output"
}

test_combined_multi_invocation_with_sequencing() {
    local responses_file="$MOCK_DIR/seq-responses.txt"
    printf '%s\n' "Iteration 1 done" "Iteration 2 done" > "$responses_file"
    export MOCK_CLAUDE_RESPONSES_FILE="$responses_file"
    export MOCK_SESSION_ID="loop-session"

    local out1 out2
    out1=$("$CLAUDE" --output-format stream-json -p "iter1")
    out2=$("$CLAUDE" --output-format stream-json -p "iter2")

    assert_output_contains "$out1" "Iteration 1 done" "First iteration response"
    assert_output_contains "$out2" "Iteration 2 done" "Second iteration response"
    assert_mock_invocation_count "2"

    local turns
    turns=$(mock_get_session_turn_count "loop-session")
    assert_equals "2" "$turns" "Session should have 2 turns"
}

# =============================================================================
# JSON Escaping Tests
# =============================================================================

test_response_with_quotes() {
    export MOCK_CLAUDE_RESPONSE='Said "hello" to the user'
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    # Should not crash - valid JSON should be produced
    assert_mock_output_valid_stream_json "$output"
}

test_response_with_newlines() {
    export MOCK_CLAUDE_RESPONSE="Line1
Line2"
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_valid_stream_json "$output"
}

test_response_with_backslash() {
    export MOCK_CLAUDE_RESPONSE='Path is C:\Users\test'
    local output
    output=$("$CLAUDE" --output-format stream-json -p "test")
    assert_mock_output_valid_stream_json "$output"
}

# =============================================================================
# CLI Reference Feature Tests
# =============================================================================

test_json_output_format() {
    export MOCK_CLAUDE_RESPONSE="JSON result"
    local output
    output=$("$CLAUDE" --output-format json -p "test")
    assert_output_contains "$output" '"type":"result"' "JSON should have result type"
    assert_output_contains "$output" '"session_id"' "JSON should have session_id"
    assert_output_contains "$output" '"cost_usd"' "JSON should have cost_usd"
    assert_output_contains "$output" "JSON result" "JSON should contain response text"
}

test_resume_short_flag() {
    # -r should work the same as --resume
    local output
    output=$("$CLAUDE" --output-format stream-json -r "short-session-id" -p "test")
    local session_id
    session_id=$(mock_extract_session_id_from_output "$output")
    assert_equals "short-session-id" "$session_id" "-r should set resume session ID"
}

test_continue_flag() {
    # -c should resume the most recent session
    export MOCK_SESSION_ID="first-session"
    "$CLAUDE" --output-format stream-json -p "first" > /dev/null

    unset MOCK_SESSION_ID
    local output
    output=$("$CLAUDE" --output-format stream-json -c -p "continue")
    local session_id
    session_id=$(mock_extract_session_id_from_output "$output")
    assert_equals "first-session" "$session_id" "-c should resume the last session"
}

test_continue_resumes_last_session() {
    # Multiple calls update last session, -c always gets the latest
    export MOCK_SESSION_ID="session-A"
    "$CLAUDE" -p "first" > /dev/null

    export MOCK_SESSION_ID="session-B"
    "$CLAUDE" -p "second" > /dev/null

    unset MOCK_SESSION_ID
    local output
    output=$("$CLAUDE" --output-format stream-json -c -p "continue")
    local session_id
    session_id=$(mock_extract_session_id_from_output "$output")
    assert_equals "session-B" "$session_id" "-c should use most recent session (B)"
}

test_no_session_persistence() {
    export MOCK_SESSION_ID="ephemeral-session"
    "$CLAUDE" --no-session-persistence -p "test" > /dev/null

    # Session file should NOT be created
    assert_file_not_exists "$MOCK_CLAUDE_LOG_DIR/sessions/ephemeral-session" \
        "Session should not be persisted"
}

test_fork_session() {
    export MOCK_SESSION_ID="original-session"
    local output
    output=$("$CLAUDE" --output-format stream-json --fork-session --resume "original-session" -p "forked")
    local session_id
    session_id=$(mock_extract_session_id_from_output "$output")

    # Forked session should start with "fork-" and contain original session ID
    assert_output_contains "$session_id" "fork-" "Forked session should have fork- prefix"
    assert_output_contains "$session_id" "original-session" "Forked session should reference original"
}

test_model_flag_parsed() {
    "$CLAUDE" --model opus --output-format stream-json -p "test" > /dev/null
    local model
    model=$(mock_get_parsed_field 1 "model")
    assert_equals "opus" "$model" "Should parse --model flag"
}

test_version_short_flag() {
    local output
    output=$("$CLAUDE" -v)
    assert_output_contains "$output" "mock" "-v should return version"
}

# =============================================================================
# Run all tests
# =============================================================================

echo "=== Mock Claude CLI Tests ==="

# Backward compat
run_test test_basic_text_output
run_test test_default_response
run_test test_version_flag
run_test test_exit_code
run_test test_fail_after_n
run_test test_simple_stream_json

# Scenarios
run_test test_scenario_simple
run_test test_scenario_multi_turn
run_test test_scenario_tool_heavy
run_test test_scenario_hit_turn_limit
run_test test_scenario_interrupted
run_test test_scenario_file_edit
run_test test_scenario_resume

# Session tracking
run_test test_session_id_from_flag
run_test test_session_id_from_resume
run_test test_session_id_from_env
run_test test_session_turn_counting
run_test test_resume_priority_over_session_id

# Max turns
run_test test_simulate_turns_default
run_test test_simulate_turns_with_scenario

# Signal exit codes
run_test test_exit_signal_sigint
run_test test_exit_signal_sigterm
run_test test_exit_signal_numeric
run_test test_exit_signal_uppercase
run_test test_exit_signal_overrides_exit_code

# File side-effects
run_test test_touch_single_file
run_test test_touch_multiple_files
run_test test_touch_modifies_existing

# Argument validation
run_test test_args_logged_correctly
run_test test_parsed_max_turns
run_test test_parsed_verbose
run_test test_parsed_user_prompt
run_test test_parsed_system_prompt
run_test test_skip_permissions_assertion
run_test test_not_received_arg

# Response sequencing
run_test test_responses_file_sequential
run_test test_responses_file_exhausted_falls_back
run_test test_responses_file_with_stream_json

# Delay
run_test test_fixed_delay
run_test test_delay_range_executes

# Tool use
run_test test_tool_use_single
run_test test_tool_use_multiple
run_test test_tool_use_custom

# Cost
run_test test_default_cost
run_test test_custom_cost

# Combined features
run_test test_combined_scenario_with_touch_and_signal
run_test test_combined_resume_with_tool_use
run_test test_combined_multi_invocation_with_sequencing

# JSON escaping
run_test test_response_with_quotes
run_test test_response_with_newlines
run_test test_response_with_backslash

# CLI reference features
run_test test_json_output_format
run_test test_resume_short_flag
run_test test_continue_flag
run_test test_continue_resumes_last_session
run_test test_no_session_persistence
run_test test_fork_session
run_test test_model_flag_parsed
run_test test_version_short_flag

print_test_summary
exit_with_test_result
