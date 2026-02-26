#!/usr/bin/env bash
# gh-error.sh - GitHub CLI error classification
#
# Provides helpers to classify gh/GitHub API errors as network errors
# (transient, should retry) vs permanent errors (should fail).
set -euo pipefail

# Prevent double-sourcing
[ -n "${_GH_ERROR_LOADED:-}" ] && return 0
_GH_ERROR_LOADED=1

# Check if an exit code and/or error output indicates a network error
#
# Network errors are transient and should trigger a retry/skip cycle.
# Non-network errors are typically permanent (auth, permission, not found).
#
# Args:
#   exit_code - Exit code from gh command (optional, can be "")
#   output    - Stderr/combined output from gh command (optional)
#
# Returns: 0 if network error detected, 1 otherwise
gh_is_network_error() {
    local exit_code="${1:-}"
    local output="${2:-}"

    # Exit code 124 = timeout
    if [ "$exit_code" = "124" ]; then
        return 0
    fi

    # Check output for network error patterns
    # shellcheck disable=SC2254
    case "$output" in
        *"Network is unreachable"*) return 0 ;;
        *"network is unreachable"*) return 0 ;;
        *"Could not resolve host"*) return 0 ;;
        *"Connection refused"*) return 0 ;;
        *"Connection timed out"*) return 0 ;;
        *"connection timed out"*) return 0 ;;
        *"Connection reset"*) return 0 ;;
        *"No route to host"*) return 0 ;;
        *"Temporary failure in name resolution"*) return 0 ;;
        *"Unable to connect"*) return 0 ;;
        *"unable to access"*) return 0 ;;
        *"Could not read from remote repository"*) return 0 ;;
        *"ssh: connect to host"*"port 22"*) return 0 ;;
        *"ssh_exchange_identification"*) return 0 ;;
        *"kex_exchange_identification"*) return 0 ;;
        *"Server refused our key"*) return 0 ;;
        *"failed to connect"*) return 0 ;;
        *"Operation timed out"*) return 0 ;;
        *"HTTP 502"*) return 0 ;;
        *"HTTP 503"*) return 0 ;;
        *"HTTP 504"*) return 0 ;;
        *"502 Bad Gateway"*) return 0 ;;
        *"503 Service Unavailable"*) return 0 ;;
        *"504 Gateway Timeout"*) return 0 ;;
        # Rate limit errors are transient and retryable
        *"API rate limit exceeded"*) return 0 ;;
        *"rate limit exceeded"*) return 0 ;;
        *"secondary rate limit"*) return 0 ;;
        *"abuse detection"*) return 0 ;;
        *"HTTP 429"*) return 0 ;;
        *"429 Too Many Requests"*) return 0 ;;
    esac

    return 1
}

# Check if an exit code and/or error output indicates a rate limit error
#
# Rate limit errors are a specific subset of transient errors where GitHub
# has throttled the client. These should trigger longer backoff (wait for
# reset) rather than standard retry.
#
# GitHub returns:
#   - HTTP 403 with "API rate limit exceeded" (primary rate limit)
#   - HTTP 403 with "secondary rate limit" (secondary/abuse rate limit)
#   - HTTP 429 (newer rate limit response)
#
# Args:
#   exit_code - Exit code from gh command (optional, can be "")
#   output    - Stderr/combined output from gh command (optional)
#
# Returns: 0 if rate limit error detected, 1 otherwise
gh_is_rate_limit_error() {
    local exit_code="${1:-}"
    local output="${2:-}"

    # shellcheck disable=SC2254
    case "$output" in
        *"API rate limit exceeded"*) return 0 ;;
        *"rate limit exceeded"*) return 0 ;;
        *"secondary rate limit"*) return 0 ;;
        *"abuse detection"*) return 0 ;;
        *"HTTP 429"*) return 0 ;;
        *"429 Too Many Requests"*) return 0 ;;
    esac

    return 1
}

# Format a user-friendly error message for GitHub CLI failures
#
# Args:
#   exit_code - Exit code from gh command
#   output    - Stderr/combined output from gh command
#   operation - Description of operation (e.g., "fetching issues")
#
# Returns: Message on stdout
gh_format_error() {
    local exit_code="$1"
    local output="$2"
    local operation="${3:-GitHub operation}"

    if gh_is_rate_limit_error "$exit_code" "$output"; then
        echo "GitHub API rate limited during $operation - will wait for reset"
    elif gh_is_network_error "$exit_code" "$output"; then
        if [ "$exit_code" = "124" ]; then
            echo "Network timeout during $operation - will retry later"
        else
            echo "Network error during $operation - will retry later"
        fi
    else
        echo "GitHub API error during $operation (exit: $exit_code)"
    fi
}

# Global flag indicating last gh operation had a network error
# Set by gh_with_network_detection, used by callers to decide retry behavior
# shellcheck disable=SC2034  # Used by callers to check error type
GH_LAST_WAS_NETWORK_ERROR=false

# Global flag indicating last gh operation hit a rate limit
# Set by gh_with_network_detection, used by callers for rate-limit-specific handling
# shellcheck disable=SC2034  # Used by callers to check error type
GH_LAST_WAS_RATE_LIMIT=false

# Execute a gh command with network error detection
#
# Runs the command and sets GH_LAST_WAS_NETWORK_ERROR and
# GH_LAST_WAS_RATE_LIMIT based on result.
# Returns the command's exit code.
#
# Args:
#   ... - gh command and arguments
#
# Returns: Command exit code
# Sets: GH_LAST_WAS_NETWORK_ERROR, GH_LAST_WAS_RATE_LIMIT
# shellcheck disable=SC2034  # GH_LAST_WAS_NETWORK_ERROR/GH_LAST_WAS_RATE_LIMIT used by callers
gh_with_network_detection() {
    GH_LAST_WAS_NETWORK_ERROR=false
    GH_LAST_WAS_RATE_LIMIT=false

    local output exit_code=0
    output=$("$@" 2>&1) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        if gh_is_rate_limit_error "$exit_code" "$output"; then
            GH_LAST_WAS_RATE_LIMIT=true
            GH_LAST_WAS_NETWORK_ERROR=true  # Rate limits are also network-retryable
        elif gh_is_network_error "$exit_code" "$output"; then
            GH_LAST_WAS_NETWORK_ERROR=true
        fi
    fi

    echo "$output"
    return "$exit_code"
}
