#!/usr/bin/env bash
# =============================================================================
# codex-backend.sh - OpenAI Codex CLI backend implementation
#
# Implements the backend interface (lib/runtime/backend-interface.sh) for
# the OpenAI Codex CLI.
#
# CLI Reference: https://developers.openai.com/codex/cli/reference
#
# Key commands:
#   codex exec        - Non-interactive execution (stable)
#   codex exec resume - Resume a previous session
#   codex login       - Authenticate (OAuth or API key)
#
# Session support: Yes (via codex exec resume)
# =============================================================================
set -euo pipefail

[ -n "${_CODEX_BACKEND_LOADED:-}" ] && return 0
_CODEX_BACKEND_LOADED=1

[ -z "${_WIGGUM_SRC_LOGGER_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/logger.sh"
[ -z "${_WIGGUM_SRC_PLATFORM_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/platform.sh"

# =============================================================================
# BACKEND IDENTITY
# =============================================================================

runtime_backend_name() {
    echo "codex"
}

# =============================================================================
# INITIALIZATION
# =============================================================================

runtime_backend_init() {
    # Codex binary (allows specifying a different binary or path)
    CODEX="${CODEX:-codex}"

    # Validate codex binary exists
    if ! command -v "$CODEX" &>/dev/null; then
        log_error "Codex backend: '$CODEX' binary not found in PATH"
        log_error "Install Codex CLI: npm install -g @openai/codex"
        log_error "Or set CODEX=/path/to/codex"
        return 1
    fi

    # Check authentication status
    if ! "$CODEX" login status &>/dev/null; then
        log_warn "Codex backend: not authenticated. Run 'codex login' first."
    fi

    # Pass through API configuration environment variables if set
    [ -n "${OPENAI_API_KEY:-}" ] && export OPENAI_API_KEY
    [ -n "${OPENAI_ORG_ID:-}" ] && export OPENAI_ORG_ID
    [ -n "${OPENAI_BASE_URL:-}" ] && export OPENAI_BASE_URL

    log_debug "Codex backend initialized (binary: $CODEX)"
}

# =============================================================================
# INVOCATION
# =============================================================================

# Invoke Codex CLI with environment-scoped auth
runtime_backend_invoke() {
    "$CODEX" "$@"
}

# =============================================================================
# ARGUMENT BUILDING
# =============================================================================

# Build CLI arguments for single-shot execution
#
# Codex exec flags:
#   --cd, -C              - workspace root
#   --full-auto           - automation preset (workspace-write + on-request)
#   --sandbox, -s         - sandbox policy
#   --dangerously-bypass  - skip all approvals (for isolated runners)
#   --json                - newline-delimited JSON output
#   --model, -m           - model override
#   --output-last-message - write final message to file
#   PROMPT                - initial instruction
runtime_backend_build_exec_args() {
    # shellcheck disable=SC2178  # nameref pattern for array population
    local -n _args="$1"
    local workspace="$2"
    local system_prompt="$3"
    local user_prompt="$4"
    # shellcheck disable=SC2034  # output_file handled by caller redirection
    local output_file="$5"
    local max_turns="$6"
    local session_id="${7:-}"

    # Base command: non-interactive execution
    _args=(exec)

    # Workspace
    _args+=(--cd "$workspace")

    # Output format: JSON for structured parsing
    _args+=(--json)

    # Automation mode for non-interactive runs
    # full-auto sets: --ask-for-approval on-request --sandbox workspace-write
    if [ "${WIGGUM_CODEX_FULL_AUTO:-true}" = "true" ]; then
        _args+=(--full-auto)
    fi

    # For CI/isolated environments, bypass all approvals
    if [ "${WIGGUM_CODEX_DANGEROUSLY_BYPASS:-false}" = "true" ]; then
        _args+=(--dangerously-bypass-approvals-and-sandbox)
    fi

    # Sandbox policy (default: workspace-write for automation)
    local sandbox="${WIGGUM_CODEX_SANDBOX:-workspace-write}"
    _args+=(--sandbox "$sandbox")

    # Model override if specified
    if [ -n "${WIGGUM_CODEX_MODEL:-}" ]; then
        _args+=(--model "$WIGGUM_CODEX_MODEL")
    fi

    # Configuration overrides via -c (for max_turns etc.)
    # Codex uses TOML config, pass key=value overrides
    if [ -n "$max_turns" ]; then
        _args+=(-c "max_turns=$max_turns")
    fi

    # Combine system prompt with user prompt (Codex accepts single prompt)
    # System context is prepended to user prompt
    local full_prompt="$user_prompt"
    if [ -n "$system_prompt" ]; then
        full_prompt="$system_prompt

$user_prompt"
    fi

    _args+=("$full_prompt")
}

# Build CLI arguments for session resume
#
# codex exec resume [SESSION_ID] [--last] [--all] [PROMPT]
runtime_backend_build_resume_args() {
    # shellcheck disable=SC2178  # nameref pattern for array population
    local -n _args="$1"
    local session_id="$2"
    local prompt="$3"
    # shellcheck disable=SC2034  # output_file handled by caller redirection
    local output_file="$4"
    local max_turns="${5:-3}"

    _args=(exec resume)

    # Session ID or --last for most recent
    if [ -n "$session_id" ] && [ "$session_id" != "last" ]; then
        _args+=("$session_id")
    else
        _args+=(--last)
    fi

    # Output format
    _args+=(--json)

    # Automation mode
    if [ "${WIGGUM_CODEX_FULL_AUTO:-true}" = "true" ]; then
        _args+=(--full-auto)
    fi

    # Configuration overrides
    if [ -n "$max_turns" ]; then
        _args+=(-c "max_turns=$max_turns")
    fi

    # Follow-up prompt
    if [ -n "$prompt" ]; then
        _args+=("$prompt")
    fi
}

# =============================================================================
# ERROR CLASSIFICATION
# =============================================================================

# Exit codes considered retryable:
#   1  - General error (may include rate limits)
#   124 - timeout (command timed out)
#
# Codex CLI doesn't document specific exit codes, so we check stderr patterns
runtime_backend_is_retryable() {
    local exit_code="$1"
    local stderr_file="$2"

    # Timeout is always retryable
    [[ "$exit_code" -eq 124 ]] && return 0

    # Exit 1 + stderr rate-limit patterns
    if [ "$exit_code" -eq 1 ] && [ -s "$stderr_file" ]; then
        local pattern
        for pattern in "429" "rate limit" "too many requests" "rate_limit" "quota exceeded"; do
            grep -qi "$pattern" "$stderr_file" 2>/dev/null && return 0
        done
    fi

    # Network errors are retryable
    if [ -s "$stderr_file" ]; then
        local pattern
        for pattern in "ECONNREFUSED" "ETIMEDOUT" "ENOTFOUND" "network error" "connection reset"; do
            grep -qi "$pattern" "$stderr_file" 2>/dev/null && return 0
        done
    fi

    return 1
}

# =============================================================================
# OUTPUT EXTRACTION
# =============================================================================

# Extract plain text from Codex CLI JSON output
#
# Codex emits newline-delimited JSON events. The final message contains
# the assistant's response.
#
# Event types include: message_start, content_block_delta, message_stop
runtime_backend_extract_text() {
    local log_file="$1"

    if [ ! -f "$log_file" ]; then
        return 1
    fi

    # Extract text from content_delta events
    # Format: {"type":"content_block_delta","delta":{"text":"..."}}
    grep '"type":"content_block_delta"' "$log_file" 2>/dev/null | \
        jq -r '.delta.text // empty' 2>/dev/null \
        || true
}

# Extract session ID from Codex CLI output
#
# Codex stores sessions in ~/.codex/sessions/ with UUID names.
# The session ID appears in the output as part of the session metadata.
runtime_backend_extract_session_id() {
    local log_file="$1"

    [ ! -f "$log_file" ] && { echo ""; return 0; }

    # Look for session_id in JSON output
    # Format: {"session_id":"<uuid>"}
    grep_pcre_match '"session_id"\s*:\s*"\K[a-f0-9-]+(?=")' "$log_file" | head -1 || true
}

# =============================================================================
# SESSION SUPPORT
# =============================================================================

runtime_backend_supports_sessions() {
    return 0  # Codex supports sessions via exec resume
}

# Codex auto-generates session IDs; we must extract from output
runtime_backend_supports_named_sessions() {
    return 1  # No --session-id flag; sessions are auto-generated
}

runtime_backend_generate_session_id() {
    # For Codex, this is called but the ID won't be used for creation
    # The actual session_id is extracted from output after the first run
    uuidgen 2>/dev/null || cat /proc/sys/kernel/random/uuid 2>/dev/null || echo "$(epoch_now)-$$-$RANDOM"
}

# =============================================================================
# USAGE TRACKING & RATE LIMITING
# =============================================================================

# Update usage statistics (placeholder - Codex doesn't expose token counts directly)
runtime_backend_usage_update() {
    local ralph_dir="${1:-}"
    # Codex CLI doesn't expose detailed token usage in the CLI output
    # Usage is tracked via the OpenAI API dashboard
    log_debug "Codex usage tracking not available via CLI"
}

# Check if rate limited (placeholder)
runtime_backend_rate_limit_check() {
    # shellcheck disable=SC2034  # ralph_dir for future use
    local ralph_dir="$1"
    # Codex handles rate limiting internally
    return 1
}

# Wait for rate limit window to reset
runtime_backend_rate_limit_wait() {
    sleep 60
}
