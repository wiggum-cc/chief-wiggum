#!/usr/bin/env bash
# mock-claude.sh - Mock Claude CLI for testing without API calls
#
# Simulates Claude CLI behavior for testing agent workflows.
# Controlled by environment variables to simulate different scenarios.
#
# Usage:
#   export CLAUDE=/path/to/mock-claude.sh
#   # Run wiggum tests
#
# Environment variables:
#   MOCK_CLAUDE_EXIT_CODE      - Exit code to return (default: 0)
#   MOCK_CLAUDE_RESPONSE       - Response text to output (single response)
#   MOCK_CLAUDE_DELAY          - Fixed seconds to delay before responding (default: 0)
#   MOCK_CLAUDE_DELAY_RANGE    - Random delay range "min-max" in seconds (e.g., "0.1-2.0")
#   MOCK_CLAUDE_FAIL_AFTER     - Fail after N invocations (for testing retries)
#   MOCK_CLAUDE_LOG_DIR        - Directory to log invocations and state
#   MOCK_CLAUDE_SCENARIO       - Named scenario: simple, multi-turn, tool-heavy,
#                                hit-turn-limit, interrupted, file-edit
#   MOCK_CLAUDE_SIMULATE_TURNS - Number of assistant turns to output (default: 1)
#   MOCK_CLAUDE_EXIT_SIGNAL    - Simulate signal exit: "sigint" (130) or "sigterm" (143)
#   MOCK_CLAUDE_TOUCH_FILES    - Colon-separated list of files to create/modify
#   MOCK_CLAUDE_RESPONSES_FILE - File with one response per line (used sequentially)
#   MOCK_CLAUDE_TOOL_USE       - Simulate tool use blocks: "bash", "edit", "write", or
#                                comma-separated list (e.g., "bash,edit")
#   MOCK_CLAUDE_COST_USD       - Cost to report in result (default: "0.01")
#   MOCK_CLAUDE_STDERR         - Text to emit on stderr before output (for testing retry)
#   MOCK_SESSION_ID            - Override session ID (default: auto-generated)
set -euo pipefail

# Resolve log directory
MOCK_LOG_DIR="${MOCK_CLAUDE_LOG_DIR:-/tmp/mock-claude}"
mkdir -p "$MOCK_LOG_DIR"

# Track invocations
MOCK_INVOCATION_COUNT_FILE="$MOCK_LOG_DIR/mock-claude-invocations"
MOCK_SESSIONS_DIR="$MOCK_LOG_DIR/sessions"
MOCK_ARGS_DIR="$MOCK_LOG_DIR/args"
mkdir -p "$MOCK_SESSIONS_DIR" "$MOCK_ARGS_DIR"

# =============================================================================
# Argument Parsing
# =============================================================================

_parsed_output_format="text"
_parsed_input_format=""
_parsed_session_id=""
_parsed_resume_id=""
_parsed_continue=false
_parsed_max_turns=""
_parsed_max_budget_usd=""
_parsed_system_prompt=""
_parsed_append_system_prompt=""
_parsed_user_prompt=""
_parsed_plugin_dir=""
_parsed_model=""
_parsed_fallback_model=""
_parsed_agent=""
_parsed_tools=""
_parsed_allowed_tools=""
_parsed_disallowed_tools=""
_parsed_permission_mode=""
_parsed_json_schema=""
_parsed_mcp_config=""
_parsed_verbose=false
_parsed_debug=""
_parsed_dangerously_skip_permissions=false
_parsed_no_session_persistence=false
_parsed_fork_session=false

_parse_args() {
    local args=("$@")
    local i=0
    while [ $i -lt ${#args[@]} ]; do
        case "${args[$i]}" in
            --output-format)
                i=$((i + 1))
                _parsed_output_format="${args[$i]:-text}"
                ;;
            --input-format)
                i=$((i + 1))
                _parsed_input_format="${args[$i]:-text}"
                ;;
            --session-id)
                i=$((i + 1))
                _parsed_session_id="${args[$i]:-}"
                ;;
            --resume|-r)
                i=$((i + 1))
                _parsed_resume_id="${args[$i]:-}"
                ;;
            --continue|-c)
                _parsed_continue=true
                ;;
            --max-turns)
                i=$((i + 1))
                _parsed_max_turns="${args[$i]:-}"
                ;;
            --max-budget-usd)
                i=$((i + 1))
                _parsed_max_budget_usd="${args[$i]:-}"
                ;;
            --system-prompt)
                i=$((i + 1))
                _parsed_system_prompt="${args[$i]:-}"
                ;;
            --system-prompt-file)
                i=$((i + 1))
                # Read from file if it exists
                if [ -f "${args[$i]:-}" ]; then
                    _parsed_system_prompt=$(cat "${args[$i]}")
                fi
                ;;
            --append-system-prompt)
                i=$((i + 1))
                _parsed_append_system_prompt="${args[$i]:-}"
                ;;
            --append-system-prompt-file)
                i=$((i + 1))
                if [ -f "${args[$i]:-}" ]; then
                    _parsed_append_system_prompt=$(cat "${args[$i]}")
                fi
                ;;
            --print|-p)
                i=$((i + 1))
                _parsed_user_prompt="${args[$i]:-}"
                ;;
            --plugin-dir)
                i=$((i + 1))
                _parsed_plugin_dir="${args[$i]:-}"
                ;;
            --model)
                i=$((i + 1))
                _parsed_model="${args[$i]:-}"
                ;;
            --fallback-model)
                i=$((i + 1))
                _parsed_fallback_model="${args[$i]:-}"
                ;;
            --agent)
                i=$((i + 1))
                _parsed_agent="${args[$i]:-}"
                ;;
            --agents)
                i=$((i + 1))
                # JSON string, just store it
                ;;
            --tools)
                i=$((i + 1))
                _parsed_tools="${args[$i]:-}"
                ;;
            --allowedTools)
                i=$((i + 1))
                _parsed_allowed_tools="${args[$i]:-}"
                ;;
            --disallowedTools)
                i=$((i + 1))
                _parsed_disallowed_tools="${args[$i]:-}"
                ;;
            --permission-mode)
                i=$((i + 1))
                _parsed_permission_mode="${args[$i]:-}"
                ;;
            --json-schema)
                i=$((i + 1))
                _parsed_json_schema="${args[$i]:-}"
                ;;
            --mcp-config)
                i=$((i + 1))
                _parsed_mcp_config="${args[$i]:-}"
                ;;
            --verbose)
                _parsed_verbose=true
                ;;
            --debug)
                i=$((i + 1))
                _parsed_debug="${args[$i]:-all}"
                ;;
            --dangerously-skip-permissions)
                _parsed_dangerously_skip_permissions=true
                ;;
            --no-session-persistence)
                _parsed_no_session_persistence=true
                ;;
            --fork-session)
                _parsed_fork_session=true
                ;;
            --version|-v)
                # Handled separately in main
                ;;
            --include-partial-messages|--chrome|--no-chrome|--ide|--init|--init-only|--maintenance)
                # Boolean flags - just acknowledge
                ;;
            --strict-mcp-config|--allow-dangerously-skip-permissions)
                # Boolean flags
                ;;
            --betas|--settings|--setting-sources|--permission-prompt-tool)
                # Flags with values - skip the value
                i=$((i + 1))
                ;;
            *)
                # Unknown arg or positional query string, skip
                ;;
        esac
        i=$((i + 1))
    done
}

# =============================================================================
# Invocation Tracking
# =============================================================================

_get_invocation_count() {
    local count=0
    if [ -f "$MOCK_INVOCATION_COUNT_FILE" ]; then
        count=$(cat "$MOCK_INVOCATION_COUNT_FILE")
    fi
    echo "$count"
}

_increment_invocation_count() {
    local count
    count=$(_get_invocation_count)
    count=$((count + 1))
    echo "$count" > "$MOCK_INVOCATION_COUNT_FILE"
    echo "$count"
}

_log_invocation() {
    local count
    count=$(_increment_invocation_count)

    # Log detailed invocation info
    local log_file="$MOCK_LOG_DIR/mock-claude-invocation-$count.log"
    {
        echo "Timestamp: $(date -Iseconds)"
        echo "Invocation: $count"
        echo "Arguments: $*"
        echo "Working Directory: $(pwd)"
        echo "---"
        echo "Parsed:"
        echo "  output_format: $_parsed_output_format"
        echo "  input_format: $_parsed_input_format"
        echo "  session_id: $_parsed_session_id"
        echo "  resume_id: $_parsed_resume_id"
        echo "  continue: $_parsed_continue"
        echo "  max_turns: $_parsed_max_turns"
        echo "  max_budget_usd: $_parsed_max_budget_usd"
        echo "  model: $_parsed_model"
        echo "  fallback_model: $_parsed_fallback_model"
        echo "  agent: $_parsed_agent"
        echo "  tools: $_parsed_tools"
        echo "  allowed_tools: $_parsed_allowed_tools"
        echo "  disallowed_tools: $_parsed_disallowed_tools"
        echo "  permission_mode: $_parsed_permission_mode"
        echo "  json_schema: ${_parsed_json_schema:+set}"
        echo "  mcp_config: $_parsed_mcp_config"
        echo "  system_prompt_length: ${#_parsed_system_prompt}"
        echo "  append_system_prompt_length: ${#_parsed_append_system_prompt}"
        echo "  user_prompt_length: ${#_parsed_user_prompt}"
        echo "  plugin_dir: $_parsed_plugin_dir"
        echo "  verbose: $_parsed_verbose"
        echo "  debug: $_parsed_debug"
        echo "  dangerously_skip_permissions: $_parsed_dangerously_skip_permissions"
        echo "  no_session_persistence: $_parsed_no_session_persistence"
        echo "  fork_session: $_parsed_fork_session"
    } > "$log_file"

    # Save raw args for assertion helpers
    local args_file="$MOCK_ARGS_DIR/invocation-$count.args"
    printf '%s\n' "$@" > "$args_file"
}

# =============================================================================
# Session Tracking
# =============================================================================

_resolve_session_id() {
    local session_id=""

    # Priority: --resume/-r > --continue/-c > --session-id > MOCK_SESSION_ID > auto-generate
    if [ -n "$_parsed_resume_id" ]; then
        session_id="$_parsed_resume_id"
    elif [ "$_parsed_continue" = true ]; then
        # Continue most recent session - use last known session or generate stable ID
        local last_session_file="$MOCK_LOG_DIR/last-session-id"
        if [ -f "$last_session_file" ]; then
            session_id=$(cat "$last_session_file")
        else
            session_id="mock-continued-session"
        fi
    elif [ -n "$_parsed_session_id" ]; then
        session_id="$_parsed_session_id"
    elif [ -n "${MOCK_SESSION_ID:-}" ]; then
        session_id="$MOCK_SESSION_ID"
    else
        session_id="mock-session-$(date +%s)-$$"
    fi

    # Handle --fork-session: create a new session but keep the reference
    if [ "$_parsed_fork_session" = true ]; then
        session_id="fork-${session_id}-$(date +%s%N)"
    fi

    # Track session state (unless --no-session-persistence)
    if [ "$_parsed_no_session_persistence" != true ]; then
        local session_file="$MOCK_SESSIONS_DIR/$session_id"
        local turn_count=0
        if [ -f "$session_file" ]; then
            turn_count=$(cat "$session_file")
        fi
        turn_count=$((turn_count + 1))
        echo "$turn_count" > "$session_file"

        # Store as last session for --continue
        echo "$session_id" > "$MOCK_LOG_DIR/last-session-id"
    fi

    echo "$session_id"
}

# =============================================================================
# Delay Simulation
# =============================================================================

_simulate_delay() {
    # Fixed delay takes priority
    if [ -n "${MOCK_CLAUDE_DELAY:-}" ] && [ "${MOCK_CLAUDE_DELAY:-0}" != "0" ]; then
        sleep "$MOCK_CLAUDE_DELAY"
        return
    fi

    # Range-based delay (jitter)
    if [ -n "${MOCK_CLAUDE_DELAY_RANGE:-}" ]; then
        local min max
        min="${MOCK_CLAUDE_DELAY_RANGE%%-*}"
        max="${MOCK_CLAUDE_DELAY_RANGE##*-}"

        # Generate random delay between min and max using awk
        local delay
        delay=$(awk -v min="$min" -v max="$max" -v seed="$RANDOM" \
            'BEGIN { srand(seed); printf "%.2f", min + rand() * (max - min) }')
        sleep "$delay"
    fi
}

# =============================================================================
# File Side-Effects
# =============================================================================

_apply_file_side_effects() {
    if [ -z "${MOCK_CLAUDE_TOUCH_FILES:-}" ]; then
        return
    fi

    # Split on colon and create/modify each file
    local IFS=':'
    local files
    read -ra files <<< "$MOCK_CLAUDE_TOUCH_FILES"
    for file in "${files[@]}"; do
        if [ -n "$file" ]; then
            mkdir -p "$(dirname "$file")"
            if [ -f "$file" ]; then
                # Append to existing file
                echo "# Modified by mock-claude at $(date -Iseconds)" >> "$file"
            else
                # Create new file
                echo "# Created by mock-claude at $(date -Iseconds)" > "$file"
            fi
        fi
    done
}

# =============================================================================
# Response Resolution
# =============================================================================

_get_response_text() {
    # Sequential responses file takes priority
    if [ -n "${MOCK_CLAUDE_RESPONSES_FILE:-}" ] && [ -f "${MOCK_CLAUDE_RESPONSES_FILE}" ]; then
        local count
        count=$(_get_invocation_count)
        local line
        line=$(sed -n "${count}p" "$MOCK_CLAUDE_RESPONSES_FILE")
        if [ -n "$line" ]; then
            echo "$line"
            return
        fi
        # Fall through to default if line doesn't exist
    fi

    echo "${MOCK_CLAUDE_RESPONSE:-Task completed successfully.}"
}

# =============================================================================
# Stream-JSON Generation
# =============================================================================

# Escape text for JSON embedding
_json_escape() {
    local text="$1"
    # Escape backslashes, double quotes, newlines, tabs
    text="${text//\\/\\\\}"
    text="${text//\"/\\\"}"
    text="${text//$'\n'/\\n}"
    text="${text//$'\t'/\\t}"
    echo "$text"
}

# Generate a tool_use block
_generate_tool_use_block() {
    local tool_name="$1"

    case "$tool_name" in
        bash)
            echo '{"type":"tool_use","id":"mock_tool_'"$(date +%s%N)"'","name":"bash","input":{"command":"echo done"}}'
            ;;
        edit)
            echo '{"type":"tool_use","id":"mock_tool_'"$(date +%s%N)"'","name":"edit","input":{"file_path":"/tmp/mock-file.txt","old_string":"old","new_string":"new"}}'
            ;;
        write)
            echo '{"type":"tool_use","id":"mock_tool_'"$(date +%s%N)"'","name":"write","input":{"file_path":"/tmp/mock-file.txt","content":"mock content"}}'
            ;;
        read)
            echo '{"type":"tool_use","id":"mock_tool_'"$(date +%s%N)"'","name":"read","input":{"file_path":"/tmp/mock-file.txt"}}'
            ;;
        *)
            echo '{"type":"tool_use","id":"mock_tool_'"$(date +%s%N)"'","name":"'"$tool_name"'","input":{}}'
            ;;
    esac
}

# Generate a single assistant message with text content
_emit_assistant_text() {
    local text="$1"
    local escaped
    escaped=$(_json_escape "$text")
    echo '{"type":"assistant","message":{"content":[{"type":"text","text":"'"$escaped"'"}]}}'
}

# Generate an assistant message with text + tool_use
_emit_assistant_with_tools() {
    local text="$1"
    shift
    local tools=("$@")

    local escaped_text
    escaped_text=$(_json_escape "$text")

    local content_parts='{"type":"text","text":"'"$escaped_text"'"}'
    for tool in "${tools[@]}"; do
        local tool_block
        tool_block=$(_generate_tool_use_block "$tool")
        content_parts="$content_parts,$tool_block"
    done

    echo '{"type":"assistant","message":{"content":['"$content_parts"']}}'
}

# Generate a tool_result message
_emit_tool_result() {
    local content="${1:-Done.}"
    local escaped
    escaped=$(_json_escape "$content")
    echo '{"type":"tool_result","content":"'"$escaped"'"}'
}

# Generate the result line
_emit_result() {
    local is_error="${1:-false}"
    local num_turns="${2:-1}"
    local cost_usd="${3:-${MOCK_CLAUDE_COST_USD:-0.01}}"
    echo '{"type":"result","is_error":'"$is_error"',"num_turns":'"$num_turns"',"cost_usd":'"$cost_usd"'}'
}

# =============================================================================
# JSON Output Generator
# =============================================================================

_generate_json() {
    local session_id="$1"
    local response="$2"
    local escaped
    escaped=$(_json_escape "$response")
    local cost="${MOCK_CLAUDE_COST_USD:-0.01}"
    local num_turns="${MOCK_CLAUDE_SIMULATE_TURNS:-1}"
    local is_error="false"

    if [ "${MOCK_CLAUDE_SCENARIO:-}" = "interrupted" ]; then
        is_error="true"
    fi

    cat <<EOF
{"type":"result","session_id":"$session_id","is_error":$is_error,"num_turns":$num_turns,"cost_usd":$cost,"result":[{"type":"text","text":"$escaped"}],"model":"${_parsed_model:-claude-sonnet-4-20250514}"}
EOF
}

# =============================================================================
# Scenario Generators
# =============================================================================

_scenario_simple() {
    local session_id="$1"
    local response="$2"

    echo '{"type":"session_start","session_id":"'"$session_id"'"}'
    _emit_assistant_text "$response"
    _emit_result "false" "1"
}

_scenario_multi_turn() {
    local session_id="$1"
    local response="$2"

    local num_turns="${MOCK_CLAUDE_SIMULATE_TURNS:-3}"

    echo '{"type":"session_start","session_id":"'"$session_id"'"}'

    local i
    for ((i = 1; i <= num_turns; i++)); do
        if [ $i -lt $num_turns ]; then
            _emit_assistant_text "Working on step $i of $num_turns..."
            _emit_tool_result "Step $i completed."
        else
            _emit_assistant_text "$response"
        fi
    done

    _emit_result "false" "$num_turns"
}

_scenario_tool_heavy() {
    local session_id="$1"
    local response="$2"

    local num_turns="${MOCK_CLAUDE_SIMULATE_TURNS:-4}"

    echo '{"type":"session_start","session_id":"'"$session_id"'"}'

    # Turn 1: read files
    _emit_assistant_with_tools "Let me examine the code." "read"
    _emit_tool_result "File contents here..."

    # Turn 2: bash command
    _emit_assistant_with_tools "Running tests." "bash"
    _emit_tool_result "All tests passed."

    # Turn 3: edit file
    _emit_assistant_with_tools "Fixing the issue." "edit"
    _emit_tool_result "File updated."

    # Turn 4: final response
    _emit_assistant_text "$response"

    _emit_result "false" "$num_turns"
}

_scenario_hit_turn_limit() {
    local session_id="$1"
    local response="$2"

    local max_turns="${_parsed_max_turns:-5}"

    echo '{"type":"session_start","session_id":"'"$session_id"'"}'

    # Fill up to max turns
    local i
    for ((i = 1; i <= max_turns; i++)); do
        if [ $i -lt $max_turns ]; then
            _emit_assistant_with_tools "Turn $i: still working..." "bash"
            _emit_tool_result "Partial result $i"
        else
            _emit_assistant_text "I've reached the turn limit. Work is still in progress: $response"
        fi
    done

    _emit_result "false" "$max_turns"
}

_scenario_interrupted() {
    local session_id="$1"
    local response="$2"

    echo '{"type":"session_start","session_id":"'"$session_id"'"}'
    _emit_assistant_text "Starting work..."
    _emit_tool_result "Partial work done."
    _emit_assistant_text "$response"
    # Result indicates error due to interruption
    _emit_result "true" "2"
}

_scenario_file_edit() {
    local session_id="$1"
    local response="$2"

    echo '{"type":"session_start","session_id":"'"$session_id"'"}'

    # Simulate reading, then editing files
    _emit_assistant_with_tools "Reading the target file." "read"
    _emit_tool_result "$(cat <<'CONTENT'
function oldCode() {
  return "old";
}
CONTENT
)"

    _emit_assistant_with_tools "Applying the fix." "edit" "write"
    _emit_tool_result "File updated successfully."

    _emit_assistant_text "$response"
    _emit_result "false" "3"
}

_scenario_resume() {
    local session_id="$1"
    local response="$2"

    # Resume scenario: no session_start, just continue
    echo '{"type":"session_start","session_id":"'"$session_id"'"}'
    _emit_assistant_text "Resuming previous session. $response"
    _emit_result "false" "1"
}

# =============================================================================
# Main Stream-JSON Generator
# =============================================================================

_generate_stream_json() {
    local session_id="$1"
    local response="$2"
    local scenario="${MOCK_CLAUDE_SCENARIO:-}"

    # If resuming and no explicit scenario, use resume scenario
    if [ -n "$_parsed_resume_id" ] && [ -z "$scenario" ]; then
        scenario="resume"
    fi

    # Route to scenario
    case "$scenario" in
        simple|"")
            # Default: check if we should add tool_use blocks
            if [ -n "${MOCK_CLAUDE_TOOL_USE:-}" ]; then
                _generate_stream_json_with_tools "$session_id" "$response"
            elif [ -n "${MOCK_CLAUDE_SIMULATE_TURNS:-}" ] && [ "${MOCK_CLAUDE_SIMULATE_TURNS:-1}" -gt 1 ]; then
                _scenario_multi_turn "$session_id" "$response"
            else
                _scenario_simple "$session_id" "$response"
            fi
            ;;
        multi-turn)
            _scenario_multi_turn "$session_id" "$response"
            ;;
        tool-heavy)
            _scenario_tool_heavy "$session_id" "$response"
            ;;
        hit-turn-limit)
            _scenario_hit_turn_limit "$session_id" "$response"
            ;;
        interrupted)
            _scenario_interrupted "$session_id" "$response"
            ;;
        file-edit)
            _scenario_file_edit "$session_id" "$response"
            ;;
        resume)
            _scenario_resume "$session_id" "$response"
            ;;
        *)
            # Unknown scenario - fall back to simple
            _scenario_simple "$session_id" "$response"
            ;;
    esac
}

# Generate stream-JSON with explicit tool_use from MOCK_CLAUDE_TOOL_USE
_generate_stream_json_with_tools() {
    local session_id="$1"
    local response="$2"

    echo '{"type":"session_start","session_id":"'"$session_id"'"}'

    # Parse tool list
    local IFS=','
    local tools
    read -ra tools <<< "${MOCK_CLAUDE_TOOL_USE}"

    # Emit assistant message with tool_use blocks
    _emit_assistant_with_tools "Executing requested operations." "${tools[@]}"

    # Emit tool results for each
    for tool in "${tools[@]}"; do
        _emit_tool_result "Result from $tool."
    done

    # Final text response
    _emit_assistant_text "$response"

    local num_turns=$((${#tools[@]} + 1))
    _emit_result "false" "$num_turns"
}

# =============================================================================
# Exit Code Resolution
# =============================================================================

_resolve_exit_code() {
    # Signal simulation takes priority
    if [ -n "${MOCK_CLAUDE_EXIT_SIGNAL:-}" ]; then
        case "${MOCK_CLAUDE_EXIT_SIGNAL}" in
            sigint|SIGINT|130)
                echo 130
                return
                ;;
            sigterm|SIGTERM|143)
                echo 143
                return
                ;;
            *)
                # Treat as raw exit code
                echo "${MOCK_CLAUDE_EXIT_SIGNAL}"
                return
                ;;
        esac
    fi

    # Scenario-based exit codes
    if [ "${MOCK_CLAUDE_SCENARIO:-}" = "interrupted" ]; then
        echo 130
        return
    fi

    # Explicit exit code
    echo "${MOCK_CLAUDE_EXIT_CODE:-0}"
}

# =============================================================================
# Main
# =============================================================================

main() {
    # Parse arguments first (before logging, so parsed values are available)
    _parse_args "$@"

    # Log the invocation with parsed args
    _log_invocation "$@"

    # Handle --version / -v
    if [[ " $* " == *" --version "* ]] || [[ " $* " == *" -v "* ]]; then
        echo "claude 1.0.0 (mock)"
        exit 0
    fi

    # Simulate delay (fixed or jitter)
    _simulate_delay

    # Check if should fail after N invocations
    if [ -n "${MOCK_CLAUDE_FAIL_AFTER:-}" ]; then
        local count
        count=$(_get_invocation_count)
        if [ "$count" -ge "$MOCK_CLAUDE_FAIL_AFTER" ]; then
            echo "Mock Claude: Simulated failure after $count invocations" >&2
            exit 1
        fi
    fi

    # Resolve session ID (handles --session-id, --resume, MOCK_SESSION_ID)
    local session_id
    session_id=$(_resolve_session_id)

    # Apply file side-effects (simulate Claude modifying files)
    _apply_file_side_effects

    # Get response text (from sequential file or env var)
    local response
    response=$(_get_response_text)

    # Emit configured stderr (for testing retry logic with rate-limit detection)
    if [ -n "${MOCK_CLAUDE_STDERR:-}" ]; then
        echo "$MOCK_CLAUDE_STDERR" >&2
    fi

    # Generate output based on format
    case "$_parsed_output_format" in
        stream-json)
            _generate_stream_json "$session_id" "$response"
            ;;
        json)
            _generate_json "$session_id" "$response"
            ;;
        *)
            echo "$response"
            ;;
    esac

    # Return the resolved exit code
    local exit_code
    exit_code=$(_resolve_exit_code)
    exit "$exit_code"
}

main "$@"
