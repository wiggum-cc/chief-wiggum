#!/usr/bin/env bash
# Tests for lib/utils/log-converter.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

# Source only the function definitions from log-converter.sh (stop before main block)
# The script lacks a BASH_SOURCE guard, so we extract functions via eval
_source_log_converter_functions() {
    local script="$WIGGUM_HOME/lib/utils/log-converter.sh"
    # Extract everything from 'set -euo pipefail' up to '# --- Main ---'
    # Use awk for portability across GNU and BSD systems
    local func_code
    func_code=$(awk '/^set -euo pipefail$/,/^# --- Main ---$/ { if (!/^# --- Main ---$/) print }' "$script")
    eval "$func_code"
}

_source_log_converter_functions

SCRIPT="$WIGGUM_HOME/lib/utils/log-converter.sh"

TEST_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# _truncate() Tests
# =============================================================================

test_truncate_short_string_unchanged() {
    local result
    result=$(_truncate "hello world" 100)
    assert_equals "hello world" "$result" "Short string should be returned unchanged"
}

test_truncate_long_string_truncates() {
    local long_str
    long_str=$(printf '%0.s-' {1..200})  # 200 chars of dashes
    local result
    result=$(_truncate "$long_str" 50)

    # Should contain the truncation message
    assert_output_contains "$result" "[... truncated 150 characters ...]" \
        "Long string should include truncation message"

    # Should NOT contain the full original string
    local first_line
    first_line=$(echo "$result" | head -1)
    assert_equals 50 "${#first_line}" "First line should be exactly max length"
}

# =============================================================================
# convert_log() Tests
# =============================================================================

test_convert_log_iteration_start_header() {
    local input="$TEST_DIR/test.log"
    local output="$TEST_DIR/output.md"

    echo '{"type":"iteration_start","iteration":1,"session_id":"abc123def456"}' > "$input"

    convert_log "$input" "$output"

    assert_file_contains "$output" "# Conversation: test" \
        "Should produce markdown header from filename"
    assert_file_contains "$output" "Iteration 1" \
        "Should show iteration number"
    assert_file_contains "$output" "abc123def456" \
        "Should show session id (truncated)"
}

test_convert_log_assistant_text() {
    local input="$TEST_DIR/test.log"
    local output="$TEST_DIR/output.md"

    echo '{"type":"assistant","message":{"content":[{"type":"text","text":"Hello world"}]}}' > "$input"

    convert_log "$input" "$output"

    assert_file_contains "$output" "## Assistant" \
        "Should produce ## Assistant section"
    assert_file_contains "$output" "Hello world" \
        "Should contain assistant text"
}

test_convert_log_tool_use_read() {
    local input="$TEST_DIR/test.log"
    local output="$TEST_DIR/output.md"

    echo '{"type":"assistant","message":{"content":[{"type":"tool_use","id":"tool1","name":"Read","input":{"file_path":"/tmp/foo.txt"}}]}}' > "$input"

    convert_log "$input" "$output"

    assert_file_contains "$output" "### Tool: Read" \
        "Should show tool name as heading"
    assert_file_contains "$output" "/tmp/foo.txt" \
        "Should show file path for Read tool"
}

test_convert_log_tool_use_bash() {
    local input="$TEST_DIR/test.log"
    local output="$TEST_DIR/output.md"

    echo '{"type":"assistant","message":{"content":[{"type":"tool_use","id":"tool2","name":"Bash","input":{"command":"ls -la /tmp"}}]}}' > "$input"

    convert_log "$input" "$output"

    assert_file_contains "$output" "### Tool: Bash" \
        "Should show Bash tool heading"
    assert_file_contains "$output" '```bash' \
        "Should wrap command in bash code block"
    assert_file_contains "$output" "ls -la /tmp" \
        "Should show the command"
}

test_convert_log_tool_use_edit() {
    local input="$TEST_DIR/test.log"
    local output="$TEST_DIR/output.md"

    echo '{"type":"assistant","message":{"content":[{"type":"tool_use","id":"tool3","name":"Edit","input":{"file_path":"/tmp/bar.sh","old_string":"echo old","new_string":"echo new"}}]}}' > "$input"

    convert_log "$input" "$output"

    assert_file_contains "$output" "### Tool: Edit" \
        "Should show Edit tool heading"
    assert_file_contains "$output" "/tmp/bar.sh" \
        "Should show file path for Edit tool"
    assert_file_contains "$output" "Old:" \
        "Should show Old: label"
    assert_file_contains "$output" "echo old" \
        "Should show old string in code block"
    assert_file_contains "$output" "New:" \
        "Should show New: label"
    assert_file_contains "$output" "echo new" \
        "Should show new string in code block"
}

test_convert_log_tool_result() {
    local input="$TEST_DIR/test.log"
    local output="$TEST_DIR/output.md"

    # Need tool_use first so pending_tools has the mapping
    cat > "$input" << 'EOF'
{"type":"assistant","message":{"content":[{"type":"tool_use","id":"tool1","name":"Read","input":{"file_path":"/tmp/foo.txt"}}]}}
{"type":"user","message":{"content":[{"type":"tool_result","tool_use_id":"tool1","content":"file contents here"}]}}
EOF

    convert_log "$input" "$output"

    assert_file_contains "$output" "**Result**" \
        "Should show Result label"
    assert_file_contains "$output" "file contents here" \
        "Should show tool result content in code block"
}

test_convert_log_iteration_complete() {
    local input="$TEST_DIR/test.log"
    local output="$TEST_DIR/output.md"

    echo '{"type":"iteration_complete","work_exit_code":0}' > "$input"

    convert_log "$input" "$output"

    assert_file_contains "$output" "Iteration completed" \
        "Should show iteration completed"
    assert_file_contains "$output" "exit code: 0" \
        "Should show exit code"
}

test_convert_log_result_stats() {
    local input="$TEST_DIR/test.log"
    local output="$TEST_DIR/output.md"

    echo '{"type":"result","total_cost_usd":0.05,"duration_ms":5000}' > "$input"

    convert_log "$input" "$output"

    assert_file_contains "$output" 'Cost: $0.05' \
        "Should show cost in stats"
    assert_file_contains "$output" "Duration: 5000ms" \
        "Should show duration in stats"
}

# =============================================================================
# convert_dir() Tests
# =============================================================================

test_convert_dir_creates_conversations_dir() {
    local worker_dir="$TEST_DIR/worker"
    mkdir -p "$worker_dir/logs"

    # Use generic step ID (could be any pipeline step)
    echo '{"type":"iteration_start","iteration":1,"session_id":"sess1"}' \
        > "$worker_dir/logs/mystep-1.log"

    convert_dir "$worker_dir" 2>/dev/null

    assert_dir_exists "$worker_dir/conversations" \
        "Should create conversations/ directory"
}

test_convert_dir_processes_agent_logs() {
    local worker_dir="$TEST_DIR/worker"
    mkdir -p "$worker_dir/logs"

    # Use generic step IDs (could be any pipeline step)
    echo '{"type":"iteration_start","iteration":1,"session_id":"sess1"}' \
        > "$worker_dir/logs/mystep-1.log"
    echo '{"type":"iteration_start","iteration":2,"session_id":"sess2"}' \
        > "$worker_dir/logs/mystep-2.log"

    convert_dir "$worker_dir" 2>/dev/null

    assert_file_exists "$worker_dir/conversations/mystep-1.md" \
        "Should create mystep-1.md"
    assert_file_exists "$worker_dir/conversations/mystep-2.md" \
        "Should create mystep-2.md"
    assert_file_contains "$worker_dir/conversations/mystep-1.md" "Iteration 1" \
        "mystep-1.md should contain iteration 1 content"
    assert_file_contains "$worker_dir/conversations/mystep-2.md" "Iteration 2" \
        "mystep-2.md should contain iteration 2 content"
}

test_convert_dir_processes_subagent_logs() {
    local worker_dir="$TEST_DIR/worker"
    mkdir -p "$worker_dir/logs"

    echo '{"type":"iteration_start","iteration":1,"session_id":"audit1"}' \
        > "$worker_dir/logs/audit-1.log"
    echo '{"type":"iteration_start","iteration":1,"session_id":"test1"}' \
        > "$worker_dir/logs/test-1.log"

    convert_dir "$worker_dir" 2>/dev/null

    assert_file_exists "$worker_dir/conversations/audit-1.md" \
        "Should create audit-1.md for sub-agent log"
    assert_file_exists "$worker_dir/conversations/test-1.md" \
        "Should create test-1.md for sub-agent log"
}

# =============================================================================
# Script Usage Tests
# =============================================================================

test_script_no_args_shows_usage() {
    local output
    output=$(bash "$SCRIPT" 2>&1 || true)
    local exit_code
    bash "$SCRIPT" >/dev/null 2>&1; exit_code=$?; true

    assert_output_contains "$output" "Usage:" \
        "No args should show usage message"
    assert_not_equals "0" "$exit_code" \
        "No args should exit with non-zero code"
}

test_script_dir_invalid_dir_exits_1() {
    local output
    output=$(bash "$SCRIPT" --dir "/nonexistent/path/xyz" 2>&1 || true)
    local exit_code=0
    bash "$SCRIPT" --dir "/nonexistent/path/xyz" >/dev/null 2>&1 || exit_code=$?

    assert_not_equals "0" "$exit_code" \
        "--dir with invalid directory should exit non-zero"
    assert_output_contains "$output" "Usage:" \
        "--dir with invalid directory should show usage"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_truncate_short_string_unchanged
run_test test_truncate_long_string_truncates
run_test test_convert_log_iteration_start_header
run_test test_convert_log_assistant_text
run_test test_convert_log_tool_use_read
run_test test_convert_log_tool_use_bash
run_test test_convert_log_tool_use_edit
run_test test_convert_log_tool_result
run_test test_convert_log_iteration_complete
run_test test_convert_log_result_stats
run_test test_convert_dir_creates_conversations_dir
run_test test_convert_dir_processes_agent_logs
run_test test_convert_dir_processes_subagent_logs
run_test test_script_no_args_shows_usage
run_test test_script_dir_invalid_dir_exits_1

print_test_summary
exit_with_test_result
