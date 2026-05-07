#!/usr/bin/env bash
# mock-helpers.sh - Test assertion helpers for mock-claude.sh
#
# Source this file in tests that use the mock Claude CLI to get convenient
# setup/teardown and assertion functions.
#
# Usage:
#   source "$TESTS_DIR/mocks/mock-helpers.sh"
#   mock_setup   # Call in test setup
#   mock_teardown # Call in test teardown
#
# Requires: test-framework.sh to be sourced first (for assert_* functions)

# =============================================================================
# Setup / Teardown
# =============================================================================

MOCK_DIR=""
MOCK_CLAUDE_PATH=""

# Initialize mock environment. Sets CLAUDE to mock, creates temp log dir.
mock_setup() {
    MOCK_DIR=$(mktemp -d)
    export MOCK_CLAUDE_LOG_DIR="$MOCK_DIR"
    MOCK_CLAUDE_PATH="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/mock-claude.sh"
    export CLAUDE="$MOCK_CLAUDE_PATH"

    # Clear any leftover env vars
    unset MOCK_CLAUDE_EXIT_CODE
    unset MOCK_CLAUDE_RESPONSE
    unset MOCK_CLAUDE_DELAY
    unset MOCK_CLAUDE_DELAY_RANGE
    unset MOCK_CLAUDE_FAIL_AFTER
    unset MOCK_CLAUDE_SCENARIO
    unset MOCK_CLAUDE_SIMULATE_TURNS
    unset MOCK_CLAUDE_EXIT_SIGNAL
    unset MOCK_CLAUDE_TOUCH_FILES
    unset MOCK_CLAUDE_RESPONSES_FILE
    unset MOCK_CLAUDE_TOOL_USE
    unset MOCK_CLAUDE_COST_USD
    unset MOCK_CLAUDE_STDERR
    unset MOCK_SESSION_ID
}

# Clean up mock temp directory
mock_teardown() {
    if [ -n "$MOCK_DIR" ] && [ -d "$MOCK_DIR" ]; then
        [ -n "$MOCK_DIR" ] && rm -rf "$MOCK_DIR"
    fi
    MOCK_DIR=""

    # Clean env vars
    unset MOCK_CLAUDE_LOG_DIR
    unset MOCK_CLAUDE_EXIT_CODE
    unset MOCK_CLAUDE_RESPONSE
    unset MOCK_CLAUDE_DELAY
    unset MOCK_CLAUDE_DELAY_RANGE
    unset MOCK_CLAUDE_FAIL_AFTER
    unset MOCK_CLAUDE_SCENARIO
    unset MOCK_CLAUDE_SIMULATE_TURNS
    unset MOCK_CLAUDE_EXIT_SIGNAL
    unset MOCK_CLAUDE_TOUCH_FILES
    unset MOCK_CLAUDE_RESPONSES_FILE
    unset MOCK_CLAUDE_TOOL_USE
    unset MOCK_CLAUDE_COST_USD
    unset MOCK_CLAUDE_STDERR
    unset MOCK_SESSION_ID
}

# Reset invocation counter without full teardown (for multi-invocation tests)
mock_reset_counter() {
    rm -f "$MOCK_CLAUDE_LOG_DIR/mock-claude-invocations"
    rm -f "$MOCK_CLAUDE_LOG_DIR"/mock-claude-invocation-*.log
    rm -f "$MOCK_CLAUDE_LOG_DIR"/args/invocation-*.args
}

# =============================================================================
# Invocation Count Assertions
# =============================================================================

# Get the number of times mock-claude was invoked
mock_get_invocation_count() {
    local count_file="$MOCK_CLAUDE_LOG_DIR/mock-claude-invocations"
    if [ -f "$count_file" ]; then
        cat "$count_file"
    else
        echo "0"
    fi
}

# Assert mock was invoked exactly N times
assert_mock_invocation_count() {
    local expected="$1"
    local message="${2:-Mock should be invoked $expected times}"
    local actual
    actual=$(mock_get_invocation_count)
    assert_equals "$expected" "$actual" "$message"
}

# =============================================================================
# Argument Assertions
# =============================================================================

# Get the raw args from invocation N (1-indexed)
mock_get_args() {
    local invocation="${1:-1}"
    local args_file="$MOCK_CLAUDE_LOG_DIR/args/invocation-$invocation.args"
    if [ -f "$args_file" ]; then
        cat "$args_file"
    fi
}

# Assert that invocation N received a specific argument
assert_mock_received_arg() {
    local invocation="$1"
    local expected_arg="$2"
    local message="${3:-Invocation $invocation should have received arg: $expected_arg}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    local args_file="$MOCK_CLAUDE_LOG_DIR/args/invocation-$invocation.args"
    if [ ! -f "$args_file" ]; then
        echo -e "  ${RED}✗${NC} $message"
        echo -e "    ${RED}No invocation $invocation recorded${NC}"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi

    if grep -qF -- "$expected_arg" "$args_file"; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message"
        echo -e "    ${RED}Expected arg: $expected_arg${NC}"
        echo -e "    ${RED}Actual args: $(tr '\n' ' ' < "$args_file")${NC}"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that invocation N did NOT receive a specific argument
assert_mock_not_received_arg() {
    local invocation="$1"
    local unexpected_arg="$2"
    local message="${3:-Invocation $invocation should NOT have received arg: $unexpected_arg}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    local args_file="$MOCK_CLAUDE_LOG_DIR/args/invocation-$invocation.args"
    if [ ! -f "$args_file" ]; then
        # No invocation means arg wasn't received
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    fi

    if grep -qF -- "$unexpected_arg" "$args_file"; then
        echo -e "  ${RED}✗${NC} $message"
        echo -e "    ${RED}Unexpected arg found: $unexpected_arg${NC}"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    else
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    fi
}

# Assert that the mock received --dangerously-skip-permissions
assert_mock_received_skip_permissions() {
    local invocation="${1:-1}"
    assert_mock_received_arg "$invocation" "--dangerously-skip-permissions" \
        "Invocation $invocation should have --dangerously-skip-permissions"
}

# Assert that the mock received --output-format stream-json
assert_mock_received_stream_json() {
    local invocation="${1:-1}"
    assert_mock_received_arg "$invocation" "--output-format" \
        "Invocation $invocation should have --output-format"
    assert_mock_received_arg "$invocation" "stream-json" \
        "Invocation $invocation should have stream-json format"
}

# Assert that the mock received --verbose
assert_mock_received_verbose() {
    local invocation="${1:-1}"
    assert_mock_received_arg "$invocation" "--verbose" \
        "Invocation $invocation should have --verbose"
}

# =============================================================================
# Session Assertions
# =============================================================================

# Get the session ID used for invocation N from the log
mock_get_session_id() {
    local invocation="${1:-1}"
    local log_file="$MOCK_CLAUDE_LOG_DIR/mock-claude-invocation-$invocation.log"
    if [ -f "$log_file" ]; then
        grep "session_id:" "$log_file" | head -1 | sed 's/.*session_id: //'
    fi
}

# Get the resume ID used for invocation N from the log
mock_get_resume_id() {
    local invocation="${1:-1}"
    local log_file="$MOCK_CLAUDE_LOG_DIR/mock-claude-invocation-$invocation.log"
    if [ -f "$log_file" ]; then
        grep "resume_id:" "$log_file" | head -1 | sed 's/.*resume_id: //'
    fi
}

# Assert that invocation N used --resume with a specific session ID
assert_mock_resumed_session() {
    local invocation="$1"
    local expected_session="$2"
    local message="${3:-Invocation $invocation should resume session: $expected_session}"
    local actual
    actual=$(mock_get_resume_id "$invocation")
    assert_equals "$expected_session" "$actual" "$message"
}

# Assert that session tracking file exists for a session ID
assert_mock_session_tracked() {
    local session_id="$1"
    local message="${2:-Session should be tracked: $session_id}"
    assert_file_exists "$MOCK_CLAUDE_LOG_DIR/sessions/$session_id" "$message"
}

# Get how many times a session has been used
mock_get_session_turn_count() {
    local session_id="$1"
    local session_file="$MOCK_CLAUDE_LOG_DIR/sessions/$session_id"
    if [ -f "$session_file" ]; then
        cat "$session_file"
    else
        echo "0"
    fi
}

# =============================================================================
# Output Assertions
# =============================================================================

# Assert that the output contains valid stream-JSON (has session_start and result)
assert_mock_output_valid_stream_json() {
    local output="$1"
    local message="${2:-Output should be valid stream-JSON}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    local has_start has_result
    has_start=$(echo "$output" | grep -c '"type":"session_start"' || true)
    has_result=$(echo "$output" | grep -c '"type":"result"' || true)

    if [ "$has_start" -ge 1 ] && [ "$has_result" -ge 1 ]; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message"
        echo -e "    ${RED}session_start count: $has_start, result count: $has_result${NC}"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that the output contains a tool_use block
assert_mock_output_has_tool_use() {
    local output="$1"
    local tool_name="${2:-}"
    local message="${3:-Output should contain tool_use${tool_name:+ for $tool_name}}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    local pattern='"type":"tool_use"'
    if [ -n "$tool_name" ]; then
        pattern='"name":"'"$tool_name"'"'
    fi

    if echo "$output" | grep -qF -- "$pattern"; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message"
        echo -e "    ${RED}Pattern not found: $pattern${NC}"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that the output contains N assistant messages
assert_mock_output_assistant_count() {
    local output="$1"
    local expected="$2"
    local message="${3:-Output should have $expected assistant messages}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    local actual
    actual=$(echo "$output" | grep -c '"type":"assistant"' || true)

    if [ "$actual" -eq "$expected" ]; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message"
        echo -e "    ${RED}Expected: $expected assistant messages${NC}"
        echo -e "    ${RED}Actual:   $actual${NC}"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that the result reports specific num_turns
assert_mock_output_num_turns() {
    local output="$1"
    local expected="$2"
    local message="${3:-Result should report $expected turns}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    local result_line
    result_line=$(echo "$output" | grep '"type":"result"' | tail -1)
    local actual
    actual=$(echo "$result_line" | grep -o '"num_turns":[0-9]*' | grep -o '[0-9]*')

    if [ "$actual" = "$expected" ]; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message"
        echo -e "    ${RED}Expected num_turns: $expected${NC}"
        echo -e "    ${RED}Actual:             $actual${NC}"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that the result reports a specific cost
assert_mock_output_cost() {
    local output="$1"
    local expected="$2"
    local message="${3:-Result should report cost $expected}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    local result_line
    result_line=$(echo "$output" | grep '"type":"result"' | tail -1)

    if echo "$result_line" | grep -q "\"cost_usd\":$expected"; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message"
        echo -e "    ${RED}Expected cost: $expected${NC}"
        echo -e "    ${RED}Result line: $result_line${NC}"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Extract the session_id from stream-JSON output
mock_extract_session_id_from_output() {
    local output="$1"
    echo "$output" | grep '"type":"session_start"' | grep -o '"session_id":"[^"]*"' | head -1 | sed 's/"session_id":"//;s/"//'
}

# =============================================================================
# Parsed Arg Assertions (from invocation log)
# =============================================================================

# Get parsed field from invocation log
mock_get_parsed_field() {
    local invocation="$1"
    local field="$2"
    local log_file="$MOCK_CLAUDE_LOG_DIR/mock-claude-invocation-$invocation.log"
    if [ -f "$log_file" ]; then
        grep "  $field:" "$log_file" | sed "s/.*$field: //"
    fi
}

# Assert that invocation N parsed a specific max_turns value
assert_mock_parsed_max_turns() {
    local invocation="$1"
    local expected="$2"
    local message="${3:-Invocation $invocation should have parsed max_turns=$expected}"
    local actual
    actual=$(mock_get_parsed_field "$invocation" "max_turns")
    assert_equals "$expected" "$actual" "$message"
}

# Assert that invocation N had --verbose
assert_mock_parsed_verbose() {
    local invocation="$1"
    local message="${2:-Invocation $invocation should have parsed verbose=true}"
    local actual
    actual=$(mock_get_parsed_field "$invocation" "verbose")
    assert_equals "true" "$actual" "$message"
}

# Assert that invocation N had a non-empty user prompt
assert_mock_had_user_prompt() {
    local invocation="$1"
    local message="${2:-Invocation $invocation should have a user prompt}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    local prompt_length
    prompt_length=$(mock_get_parsed_field "$invocation" "user_prompt_length")

    if [ -n "$prompt_length" ] && [ "$prompt_length" -gt 0 ]; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message"
        echo -e "    ${RED}User prompt length: ${prompt_length:-0}${NC}"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that invocation N had a non-empty system prompt (--system-prompt or --append-system-prompt)
assert_mock_had_system_prompt() {
    local invocation="$1"
    local message="${2:-Invocation $invocation should have a system prompt}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    local sys_length append_length
    sys_length=$(mock_get_parsed_field "$invocation" "system_prompt_length")
    append_length=$(mock_get_parsed_field "$invocation" "append_system_prompt_length")

    if { [ -n "$sys_length" ] && [ "$sys_length" -gt 0 ]; } || \
       { [ -n "$append_length" ] && [ "$append_length" -gt 0 ]; }; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message"
        echo -e "    ${RED}System prompt length: ${sys_length:-0}, Append system prompt length: ${append_length:-0}${NC}"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}
