#!/usr/bin/env bash
# =============================================================================
# opencode-backend.sh - OpenCode backend skeleton
#
# Stub implementation of the backend interface (lib/runtime/backend-interface.sh)
# for the OpenCode CLI. Each function has a documented TODO for implementors.
#
# To complete this backend:
#   1. Implement each TODO function
#   2. Test with: WIGGUM_RUNTIME_BACKEND=opencode wiggum run
#   3. See docs/RUNTIME-SCHEMA.md for the full backend contract
# =============================================================================
set -euo pipefail

[ -n "${_OPENCODE_BACKEND_LOADED:-}" ] && return 0
_OPENCODE_BACKEND_LOADED=1

[ -z "${_WIGGUM_SRC_LOGGER_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/logger.sh"

# Fail-fast helper for unimplemented functions
#
# Provides clear error message when OpenCode backend functions are called
# without implementation.
_opencode_not_implemented() {
    local func_name="${1:-unknown}"
    log_error "OpenCode backend: $func_name is not implemented"
    log_error "To implement OpenCode backend, edit: $WIGGUM_HOME/lib/backend/opencode/opencode-backend.sh"
    log_error "See docs/RUNTIME-SCHEMA.md for the backend contract"
    return 1
}

# =============================================================================
# BACKEND IDENTITY
# =============================================================================

runtime_backend_name() {
    echo "opencode"
}

# =============================================================================
# INITIALIZATION
# =============================================================================

runtime_backend_init() {
    OPENCODE="${OPENCODE:-opencode}"
    
    # Validate opencode binary exists
    if ! command -v "$OPENCODE" &>/dev/null; then
        log_error "OpenCode backend: '$OPENCODE' binary not found in PATH"
        log_error "Install OpenCode or set OPENCODE=/path/to/opencode"
        return 1
    fi
    
    log_debug "OpenCode backend initialized (binary: $OPENCODE)"
}

# =============================================================================
# INVOCATION
# =============================================================================

runtime_backend_invoke() {
    # TODO: Invoke OpenCode CLI with appropriate auth scoping
    # Example: OPENCODE_API_KEY="$_TOKEN" "$OPENCODE" "$@"
    "$OPENCODE" "$@"
}

# =============================================================================
# ARGUMENT BUILDING
# =============================================================================

runtime_backend_build_exec_args() {
    _opencode_not_implemented "build_exec_args"
}

runtime_backend_build_resume_args() {
    _opencode_not_implemented "build_resume_args"
}

# =============================================================================
# ERROR CLASSIFICATION
# =============================================================================

runtime_backend_is_retryable() {
    # shellcheck disable=SC2034  # Args defined for implementors to use
    local exit_code="$1" stderr_file="$2"

    # TODO: Define OpenCode-specific retryable exit codes and error patterns
    # Example:
    #   [[ "$exit_code" -eq 5 || "$exit_code" -eq 124 ]] && return 0
    #   if [ "$exit_code" -eq 1 ] && [ -s "$stderr_file" ]; then
    #       grep -qi "rate limit" "$stderr_file" 2>/dev/null && return 0
    #   fi
    return 1  # Conservative default: nothing is retryable
}

# =============================================================================
# OUTPUT EXTRACTION
# =============================================================================

runtime_backend_extract_text() {
    _opencode_not_implemented "extract_text"
}

runtime_backend_extract_session_id() {
    # shellcheck disable=SC2034  # log_file for implementors
    local log_file="$1"

    # TODO: Extract session ID from OpenCode output (if applicable)
    echo ""
}

# =============================================================================
# SESSION SUPPORT
# =============================================================================

runtime_backend_supports_sessions() {
    # TODO: Set to 0 (return 0) if OpenCode supports session resumption
    return 1  # Default: no session support
}
