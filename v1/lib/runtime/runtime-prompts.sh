#!/usr/bin/env bash
# =============================================================================
# runtime-prompts.sh - Configurable prompt wrappers for runtime layer
#
# Provides pre/post wrappers for system and user prompts. Wrappers are
# defined per backend in config and applied to all agent work invocations
# (not summary/supervisor phases).
#
# Config location: runtime.backends.<backend>.prompts in config.json
# Values starting with @ are file paths relative to $WIGGUM_HOME.
#
# Resolution priority:
#   1. Environment variables (WIGGUM_PROMPT_PRE_SYSTEM, etc.)
#   2. .ralph/config.json
#   3. config/config.json
#   4. Empty string (no wrapping)
#
# Public API:
#   runtime_prompts_init(backend)   - Load prompt config for active backend
#   runtime_wrap_system(prompt)     - Return system prompt with pre/post wrappers
#   runtime_wrap_user(prompt)       - Return user prompt with pre/post wrappers
# =============================================================================
set -euo pipefail

[ -n "${_RUNTIME_PROMPTS_LOADED:-}" ] && return 0
_RUNTIME_PROMPTS_LOADED=1

[ -z "${_WIGGUM_SRC_LOGGER_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/logger.sh"

# Module-level cached prompt values
_PROMPT_PRE_SYSTEM=""
_PROMPT_POST_SYSTEM=""
_PROMPT_PRE_USER=""
_PROMPT_POST_USER=""
_PROMPTS_INITIALIZED=0

# Resolve a prompt value - if it starts with @, read from file; otherwise return literal
#
# Args:
#   value - The raw prompt value (literal string or @filepath)
#
# Returns: Resolved string via stdout
_runtime_resolve_prompt_value() {
    local value="$1"

    # Empty value
    if [ -z "$value" ]; then
        echo ""
        return 0
    fi

    # File reference: @path/to/file (relative to WIGGUM_HOME)
    if [[ "$value" == @* ]]; then
        local file_path="${value#@}"
        # Resolve relative to WIGGUM_HOME
        if [[ "$file_path" != /* ]]; then
            file_path="$WIGGUM_HOME/$file_path"
        fi

        if [ -f "$file_path" ]; then
            cat "$file_path"
        else
            log_warn "Prompt file not found: $file_path (from value: $value)"
            echo ""
        fi
        return 0
    fi

    # Literal string
    echo "$value"
}

# Load a single prompt key from config files
#
# Args:
#   backend - Backend name (e.g., "claude")
#   key     - Prompt key (e.g., "pre_system")
#
# Returns: Raw config value via stdout (before @file resolution)
_runtime_load_prompt_from_config() {
    local backend="$1"
    local key="$2"
    local value=""

    # Check project-level config first
    if [ -z "$value" ] && [ -f "${RALPH_DIR:-}/.ralph/config.json" ]; then
        value=$(jq -r ".runtime.backends.${backend}.prompts.${key} // empty" "${RALPH_DIR}/.ralph/config.json" 2>/dev/null) || true
    fi

    # Check global config
    if [ -z "$value" ] && [ -f "$WIGGUM_HOME/config/config.json" ]; then
        value=$(jq -r ".runtime.backends.${backend}.prompts.${key} // empty" "$WIGGUM_HOME/config/config.json" 2>/dev/null) || true
    fi

    echo "$value"
}

# Initialize prompt wrappers for the active backend
#
# Loads prompt config from env vars, project config, and global config.
# Resolves @file references. Caches resolved values in module-level vars.
#
# Args:
#   backend - The active backend name (e.g., "claude")
runtime_prompts_init() {
    [ "$_PROMPTS_INITIALIZED" -eq 1 ] && return 0

    local backend="${1:-claude}"
    local raw_value=""

    # Pre-system prompt
    raw_value="${WIGGUM_PROMPT_PRE_SYSTEM:-}"
    if [ -z "$raw_value" ]; then
        raw_value=$(_runtime_load_prompt_from_config "$backend" "pre_system")
    fi
    _PROMPT_PRE_SYSTEM=$(_runtime_resolve_prompt_value "$raw_value")

    # Post-system prompt
    raw_value="${WIGGUM_PROMPT_POST_SYSTEM:-}"
    if [ -z "$raw_value" ]; then
        raw_value=$(_runtime_load_prompt_from_config "$backend" "post_system")
    fi
    _PROMPT_POST_SYSTEM=$(_runtime_resolve_prompt_value "$raw_value")

    # Pre-user prompt
    raw_value="${WIGGUM_PROMPT_PRE_USER:-}"
    if [ -z "$raw_value" ]; then
        raw_value=$(_runtime_load_prompt_from_config "$backend" "pre_user")
    fi
    _PROMPT_PRE_USER=$(_runtime_resolve_prompt_value "$raw_value")

    # Post-user prompt
    raw_value="${WIGGUM_PROMPT_POST_USER:-}"
    if [ -z "$raw_value" ]; then
        raw_value=$(_runtime_load_prompt_from_config "$backend" "post_user")
    fi
    _PROMPT_POST_USER=$(_runtime_resolve_prompt_value "$raw_value")

    _PROMPTS_INITIALIZED=1

    if [ -n "$_PROMPT_PRE_SYSTEM" ] || [ -n "$_PROMPT_POST_SYSTEM" ] || \
       [ -n "$_PROMPT_PRE_USER" ] || [ -n "$_PROMPT_POST_USER" ]; then
        log_debug "Prompt wrappers loaded for backend: $backend"
    fi
}

# Wrap a system prompt with pre/post wrappers
#
# Args:
#   prompt - The original system prompt
#
# Returns: Wrapped prompt via stdout
runtime_wrap_system() {
    local prompt="$1"
    local result=""

    if [ -n "$_PROMPT_PRE_SYSTEM" ]; then
        result="${_PROMPT_PRE_SYSTEM}
${prompt}"
    else
        result="$prompt"
    fi

    if [ -n "$_PROMPT_POST_SYSTEM" ]; then
        result="${result}
${_PROMPT_POST_SYSTEM}"
    fi

    echo "$result"
}

# Wrap a user prompt with pre/post wrappers
#
# Args:
#   prompt - The original user prompt
#
# Returns: Wrapped prompt via stdout
runtime_wrap_user() {
    local prompt="$1"
    local result=""

    if [ -n "$_PROMPT_PRE_USER" ]; then
        result="${_PROMPT_PRE_USER}
${prompt}"
    else
        result="$prompt"
    fi

    if [ -n "$_PROMPT_POST_USER" ]; then
        result="${result}
${_PROMPT_POST_USER}"
    fi

    echo "$result"
}
