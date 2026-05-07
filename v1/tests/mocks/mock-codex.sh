#!/usr/bin/env bash
# mock-codex.sh - Mock OpenAI Codex CLI for testing without API calls
#
# Simulates Codex CLI behavior for testing agent workflows.
# Controlled by environment variables to simulate different scenarios.
#
# Usage:
#   export CODEX=/path/to/mock-codex.sh
#   # Run wiggum tests
#
# Commands:
#   exec [options] <prompt>           - Non-interactive execution
#   exec resume [session_id] <prompt> - Resume a session
#   login status                      - Check authentication status
#
# Environment variables:
#   MOCK_CODEX_EXIT_CODE      - Exit code to return (default: 0)
#   MOCK_CODEX_RESPONSE       - Response text to output
#   MOCK_CODEX_DELAY          - Fixed seconds to delay before responding
#   MOCK_CODEX_FAIL_AFTER     - Fail after N invocations
#   MOCK_CODEX_LOG_DIR        - Directory to log invocations and state
#   MOCK_CODEX_SCENARIO       - Named scenario: simple, multi-turn, rate-limit
#   MOCK_CODEX_SESSION_ID     - Override auto-generated session ID
#   MOCK_CODEX_STDERR         - Text to emit on stderr (for testing retry)
#   MOCK_CODEX_COST_USD       - Cost to report (default: "0.01")
set -euo pipefail

# Resolve log directory
MOCK_LOG_DIR="${MOCK_CODEX_LOG_DIR:-/tmp/mock-codex}"
mkdir -p "$MOCK_LOG_DIR"

# Track invocations
MOCK_INVOCATION_COUNT_FILE="$MOCK_LOG_DIR/mock-codex-invocations"
MOCK_SESSIONS_DIR="$MOCK_LOG_DIR/sessions"
MOCK_ARGS_DIR="$MOCK_LOG_DIR/args"
mkdir -p "$MOCK_SESSIONS_DIR" "$MOCK_ARGS_DIR"

# =============================================================================
# Argument Parsing
# =============================================================================

_parsed_command=""
_parsed_subcommand=""
_parsed_cd=""
_parsed_json=false
_parsed_full_auto=false
_parsed_sandbox=""
_parsed_model=""
_parsed_max_turns=""
_parsed_session_id=""
_parsed_resume=false
_parsed_last=false
_parsed_config_overrides=()
_parsed_prompt=""

_parse_args() {
    local args=("$@")
    local i=0

    # First arg is the main command
    if [ $i -lt ${#args[@]} ]; then
        _parsed_command="${args[$i]}"
        i=$((i + 1))
    fi

    # Handle subcommands
    if [ "$_parsed_command" = "exec" ] && [ $i -lt ${#args[@]} ]; then
        local next="${args[$i]}"
        if [ "$next" = "resume" ]; then
            _parsed_subcommand="resume"
            _parsed_resume=true
            i=$((i + 1))
        fi
    fi

    # Parse flags
    while [ $i -lt ${#args[@]} ]; do
        case "${args[$i]}" in
            --cd|-C)
                _parsed_cd="${args[$((i + 1))]:-}"
                i=$((i + 2))
                ;;
            --json)
                _parsed_json=true
                i=$((i + 1))
                ;;
            --full-auto)
                _parsed_full_auto=true
                i=$((i + 1))
                ;;
            --sandbox|-s)
                _parsed_sandbox="${args[$((i + 1))]:-workspace-write}"
                i=$((i + 2))
                ;;
            --model|-m)
                _parsed_model="${args[$((i + 1))]:-}"
                i=$((i + 2))
                ;;
            --last)
                _parsed_last=true
                i=$((i + 1))
                ;;
            -c)
                i=$((i + 1))
                _parsed_config_overrides+=("${args[$i]:-}")
                # Extract max_turns from config override
                if [[ "${args[$i]:-}" == max_turns=* ]]; then
                    _parsed_max_turns="${args[$i]#max_turns=}"
                fi
                ;;
            -*)
                # Unknown flag - skip
                i=$((i + 1))
                ;;
            *)
                # Positional argument - could be session_id or prompt
                if [ "$_parsed_resume" = true ] && [ -z "$_parsed_session_id" ] && [[ "${args[$i]}" != -* ]]; then
                    # First positional after "exec resume" could be session_id
                    # Check if it looks like a UUID
                    if [[ "${args[$i]}" =~ ^[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}$ ]]; then
                        _parsed_session_id="${args[$i]}"
                        i=$((i + 1))
                        continue
                    fi
                fi
                # Otherwise it's the prompt (collect all remaining args)
                if [ -z "$_parsed_prompt" ]; then
                    _parsed_prompt="${args[$i]}"
                else
                    _parsed_prompt="$_parsed_prompt ${args[$i]}"
                fi
                i=$((i + 1))
                ;;
        esac
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

    local log_file="$MOCK_LOG_DIR/invocation-$count.log"
    {
        echo "=== Mock Codex Invocation $count ==="
        echo "timestamp: $(date -Iseconds)"
        echo "args: $*"
        echo "parsed:"
        echo "  command: $_parsed_command"
        echo "  subcommand: $_parsed_subcommand"
        echo "  cd: $_parsed_cd"
        echo "  json: $_parsed_json"
        echo "  full_auto: $_parsed_full_auto"
        echo "  sandbox: $_parsed_sandbox"
        echo "  model: $_parsed_model"
        echo "  max_turns: $_parsed_max_turns"
        echo "  session_id: $_parsed_session_id"
        echo "  resume: $_parsed_resume"
        echo "  last: $_parsed_last"
        echo "  config_overrides: ${_parsed_config_overrides[*]}"
        echo "  prompt: ${_parsed_prompt:0:100}..."
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

    if [ "$_parsed_resume" = true ]; then
        if [ -n "$_parsed_session_id" ]; then
            session_id="$_parsed_session_id"
        elif [ "$_parsed_last" = true ]; then
            # Get last session
            local last_session_file="$MOCK_LOG_DIR/last-session-id"
            if [ -f "$last_session_file" ]; then
                session_id=$(cat "$last_session_file")
            else
                session_id="mock-last-session-not-found"
            fi
        fi
    else
        # New session - auto-generate or use override
        if [ -n "${MOCK_CODEX_SESSION_ID:-}" ]; then
            session_id="$MOCK_CODEX_SESSION_ID"
        else
            # Generate a UUID-like session ID
            session_id="$(cat /proc/sys/kernel/random/uuid 2>/dev/null || uuidgen 2>/dev/null || echo "$(date +%s)-$$-$(shuf -i 1000-9999 -n 1)")"
        fi
    fi

    # Track session state
    local session_file="$MOCK_SESSIONS_DIR/$session_id"
    local turn_count=0
    if [ -f "$session_file" ]; then
        turn_count=$(cat "$session_file")
    fi
    turn_count=$((turn_count + 1))
    echo "$turn_count" > "$session_file"

    # Store as last session
    echo "$session_id" > "$MOCK_LOG_DIR/last-session-id"

    echo "$session_id"
}

# =============================================================================
# Delay Simulation
# =============================================================================

_simulate_delay() {
    if [ -n "${MOCK_CODEX_DELAY:-}" ] && [ "${MOCK_CODEX_DELAY:-0}" != "0" ]; then
        sleep "$MOCK_CODEX_DELAY"
    fi
}

# =============================================================================
# JSON Helpers
# =============================================================================

_json_escape() {
    local text="$1"
    text="${text//\\/\\\\}"
    text="${text//\"/\\\"}"
    text="${text//$'\n'/\\n}"
    text="${text//$'\t'/\\t}"
    echo "$text"
}

# =============================================================================
# JSON Output Generator (Codex-style JSONL)
# =============================================================================

# Codex emits JSONL events similar to OpenAI's streaming API
# Event types: session_start, content_block_start, content_block_delta, content_block_stop, message_stop

_generate_jsonl() {
    local session_id="$1"
    local response="$2"
    local escaped
    escaped=$(_json_escape "$response")
    local cost="${MOCK_CODEX_COST_USD:-0.05}"
    local model="${_parsed_model:-gpt-5-codex}"

    # Session start event (contains session_id for extraction)
    echo "{\"type\":\"session_start\",\"session_id\":\"$session_id\",\"model\":\"$model\"}"

    # Message start
    echo "{\"type\":\"message_start\",\"message\":{\"id\":\"msg-$(date +%s)\",\"role\":\"assistant\",\"content\":[]}}"

    # Content block start
    echo "{\"type\":\"content_block_start\",\"index\":0,\"content_block\":{\"type\":\"text\",\"text\":\"\"}}"

    # Content delta (the actual response text)
    echo "{\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"$escaped\"}}"

    # Content block stop
    echo "{\"type\":\"content_block_stop\",\"index\":0}"

    # Message stop with usage
    echo "{\"type\":\"message_stop\",\"usage\":{\"input_tokens\":100,\"output_tokens\":50,\"total_tokens\":150},\"cost_usd\":$cost}"

    # Final result
    echo "{\"type\":\"result\",\"session_id\":\"$session_id\",\"is_error\":false}"
}

# =============================================================================
# Scenario Generators
# =============================================================================

_scenario_simple() {
    local session_id="$1"
    local response="$2"
    _generate_jsonl "$session_id" "$response"
}

_scenario_rate_limit() {
    # Simulate rate limit error
    echo "{\"type\":\"error\",\"error\":{\"type\":\"rate_limit_error\",\"message\":\"Rate limit exceeded. Please wait and retry.\"}}" >&2
    return 1
}

_scenario_multi_turn() {
    local session_id="$1"
    local response="$2"
    local num_turns="${MOCK_CODEX_TURNS:-3}"

    # First turn with session_id
    echo "{\"type\":\"session_start\",\"session_id\":\"$session_id\",\"model\":\"${_parsed_model:-gpt-5-codex}\"}"

    for ((i = 1; i <= num_turns; i++)); do
        local turn_text
        if [ "$i" -lt "$num_turns" ]; then
            turn_text="Working on step $i of $num_turns..."
        else
            turn_text="$response"
        fi

        local escaped
        escaped=$(_json_escape "$turn_text")

        echo "{\"type\":\"message_start\",\"message\":{\"id\":\"msg-$i\",\"role\":\"assistant\"}}"
        echo "{\"type\":\"content_block_start\",\"index\":0,\"content_block\":{\"type\":\"text\"}}"
        echo "{\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"text\":\"$escaped\"}}"
        echo "{\"type\":\"content_block_stop\",\"index\":0}"
        echo "{\"type\":\"message_stop\"}"
    done

    echo "{\"type\":\"result\",\"session_id\":\"$session_id\",\"is_error\":false}"
}

_scenario_resume() {
    local session_id="$1"
    local response="$2"

    # Resume doesn't emit session_start with new session_id
    # It continues the existing session
    echo "{\"type\":\"message_start\",\"message\":{\"id\":\"msg-resume\",\"role\":\"assistant\"}}"

    local escaped
    escaped=$(_json_escape "Resuming session. $response")

    echo "{\"type\":\"content_block_start\",\"index\":0,\"content_block\":{\"type\":\"text\"}}"
    echo "{\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"text\":\"$escaped\"}}"
    echo "{\"type\":\"content_block_stop\",\"index\":0}"
    echo "{\"type\":\"message_stop\"}"
    echo "{\"type\":\"result\",\"session_id\":\"$session_id\",\"is_error\":false}"
}

# =============================================================================
# Main Output Generator
# =============================================================================

_generate_output() {
    local session_id="$1"
    local response="$2"
    local scenario="${MOCK_CODEX_SCENARIO:-}"

    # If resuming and no explicit scenario, use resume scenario
    if [ "$_parsed_resume" = true ] && [ -z "$scenario" ]; then
        scenario="resume"
    fi

    case "$scenario" in
        simple|"")
            _scenario_simple "$session_id" "$response"
            ;;
        rate-limit)
            _scenario_rate_limit
            ;;
        multi-turn)
            _scenario_multi_turn "$session_id" "$response"
            ;;
        resume)
            _scenario_resume "$session_id" "$response"
            ;;
        *)
            _scenario_simple "$session_id" "$response"
            ;;
    esac
}

# =============================================================================
# Exit Code Resolution
# =============================================================================

_resolve_exit_code() {
    # Scenario-based exit codes
    case "${MOCK_CODEX_SCENARIO:-}" in
        rate-limit)
            echo 1
            return
            ;;
    esac

    # Explicit exit code
    echo "${MOCK_CODEX_EXIT_CODE:-0}"
}

# =============================================================================
# Command Handlers
# =============================================================================

_handle_login() {
    if [ "$_parsed_subcommand" = "status" ] || [ "${1:-}" = "status" ]; then
        echo "Logged in as mock-user@example.com"
        exit 0
    fi
    echo "Mock login successful"
    exit 0
}

_handle_exec() {
    # Simulate delay
    _simulate_delay

    # Check if should fail after N invocations
    if [ -n "${MOCK_CODEX_FAIL_AFTER:-}" ]; then
        local count
        count=$(_get_invocation_count)
        if [ "$count" -ge "$MOCK_CODEX_FAIL_AFTER" ]; then
            echo "Mock Codex: Simulated failure after $count invocations" >&2
            exit 1
        fi
    fi

    # Resolve session ID
    local session_id
    session_id=$(_resolve_session_id)

    # Get response text
    local response="${MOCK_CODEX_RESPONSE:-Task completed successfully.}"

    # Emit configured stderr (for testing retry logic)
    if [ -n "${MOCK_CODEX_STDERR:-}" ]; then
        echo "$MOCK_CODEX_STDERR" >&2
    fi

    # Generate output based on format
    if [ "$_parsed_json" = true ]; then
        _generate_output "$session_id" "$response"
    else
        echo "$response"
    fi

    # Return the resolved exit code
    local exit_code
    exit_code=$(_resolve_exit_code)
    exit "$exit_code"
}

# =============================================================================
# Main
# =============================================================================

main() {
    # Parse arguments first
    _parse_args "$@"

    # Log the invocation
    _log_invocation "$@"

    # Handle version
    if [[ " $* " == *" --version "* ]]; then
        echo "codex 1.0.0 (mock)"
        exit 0
    fi

    # Route to command handler
    case "$_parsed_command" in
        login)
            shift
            _handle_login "$@"
            ;;
        exec)
            _handle_exec
            ;;
        "")
            # No command - show help
            echo "Usage: codex <command> [options]" >&2
            echo "Commands: exec, login" >&2
            exit 1
            ;;
        *)
            echo "Unknown command: $_parsed_command" >&2
            exit 1
            ;;
    esac
}

main "$@"
