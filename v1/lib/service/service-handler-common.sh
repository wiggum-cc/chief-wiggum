#!/usr/bin/env bash
# service-handler-common.sh - Common utilities for service handlers
#
# Provides standardized helpers for service handler implementations:
# - Validation (env vars, files, dirs)
# - Conditional execution
# - Timing and logging wrappers
# - Graceful failure handling
set -euo pipefail

[ -n "${_SVC_HANDLER_COMMON_LOADED:-}" ] && return 0
_SVC_HANDLER_COMMON_LOADED=1

[ -z "${_WIGGUM_SRC_LOGGER_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/logger.sh"

# Validate required environment variables are set and non-empty
#
# Args:
#   ... - Variable names to check
#
# Returns: 0 if all set, 1 if any missing (with error log)
#
# Usage:
#   svc_require_env RALPH_DIR PROJECT_DIR || return 1
svc_require_env() {
    local missing=()
    for var in "$@"; do
        if [ -z "${!var:-}" ]; then
            missing+=("$var")
        fi
    done
    
    if [ ${#missing[@]} -gt 0 ]; then
        log_error "Service handler missing required env: ${missing[*]}"
        return 1
    fi
    return 0
}

# Validate required files exist
#
# Args:
#   ... - File paths to check
#
# Returns: 0 if all exist, 1 if any missing
svc_require_files() {
    local missing=()
    for file in "$@"; do
        if [ ! -f "$file" ]; then
            missing+=("$file")
        fi
    done
    
    if [ ${#missing[@]} -gt 0 ]; then
        log_error "Service handler missing required files: ${missing[*]}"
        return 1
    fi
    return 0
}

# Validate required directories exist
#
# Args:
#   ... - Directory paths to check
#
# Returns: 0 if all exist, 1 if any missing
svc_require_dirs() {
    local missing=()
    for dir in "$@"; do
        if [ ! -d "$dir" ]; then
            missing+=("$dir")
        fi
    done
    
    if [ ${#missing[@]} -gt 0 ]; then
        log_error "Service handler missing required dirs: ${missing[*]}"
        return 1
    fi
    return 0
}

# Run function only if condition variable is true
#
# Args:
#   condition_var - Name of variable to check (should be "true" to run)
#   func          - Function to call
#   ...           - Arguments to pass to function
#
# Returns: 0 if skipped or function succeeded, function's exit code otherwise
#
# Usage:
#   svc_run_if POOL_CLEANUP_EVENT orch_process_pending_merges
svc_run_if() {
    local condition_var="$1"
    local func="$2"
    shift 2
    
    if [[ "${!condition_var:-false}" == "true" ]]; then
        "$func" "$@"
    else
        return 0
    fi
}

# Run function if any of multiple conditions are true
#
# Args:
#   func      - Function to call
#   ...       - Condition variable names (any true triggers run)
#
# Returns: 0 if skipped, function exit code otherwise
#
# Usage:
#   svc_run_if_any orch_process_pending_merges POOL_CLEANUP_EVENT SCHED_SCHEDULING_EVENT
svc_run_if_any() {
    local func="$1"
    shift
    
    for condition_var in "$@"; do
        if [[ "${!condition_var:-false}" == "true" ]]; then
            "$func"
            return $?
        fi
    done
    return 0
}

# Wrap function with timing and debug logging
#
# Args:
#   name - Service/handler name for logging
#   func - Function to call
#   ...  - Arguments to pass
#
# Returns: Function's exit code
svc_wrap() {
    local name="$1"
    local func="$2"
    shift 2
    
    local start_time end_time duration exit_code=0
    start_time=$(date +%s%N 2>/dev/null || date +%s)
    
    log_debug "svc_wrap: Starting $name"
    "$func" "$@" || exit_code=$?
    
    end_time=$(date +%s%N 2>/dev/null || date +%s)
    if [[ "$start_time" =~ ^[0-9]{10,}$ ]]; then
        duration=$(( (end_time - start_time) / 1000000 ))
        log_debug "svc_wrap: $name completed in ${duration}ms (exit: $exit_code)"
    else
        duration=$((end_time - start_time))
        log_debug "svc_wrap: $name completed in ${duration}s (exit: $exit_code)"
    fi
    
    return "$exit_code"
}

# Run function with graceful failure handling
#
# Catches failures, logs them, but returns 0 to allow service to continue.
# Use for optional/non-critical operations.
#
# Args:
#   name - Operation name for logging
#   func - Function to call
#   ...  - Arguments to pass
#
# Returns: Always 0, but logs if function failed
svc_try() {
    local name="$1"
    local func="$2"
    shift 2
    
    local exit_code=0
    "$func" "$@" || exit_code=$?
    
    if [ "$exit_code" -ne 0 ]; then
        log_warn "svc_try: $name failed (exit $exit_code) - continuing"
    fi
    
    return 0
}

# Run function suppressing output unless it fails
#
# Args:
#   func - Function to call
#   ...  - Arguments
#
# Returns: Function's exit code
svc_quiet() {
    local func="$1"
    shift
    
    local output exit_code=0
    output=$("$func" "$@" 2>&1) || exit_code=$?
    
    if [ "$exit_code" -ne 0 ]; then
        echo "$output" >&2
    fi
    
    return "$exit_code"
}

# Create standard service handler that wraps an existing function
#
# This is a code generation helper - outputs a handler function definition.
# Useful for batch-generating simple pass-through handlers.
#
# Args:
#   handler_name - Name of handler function (svc_*)
#   impl_func    - Implementation function to wrap
#
# Outputs: Function definition to stdout (can be eval'd or redirected)
svc_generate_handler() {
    local handler_name="$1"
    local impl_func="$2"
    
    cat <<EOF
$handler_name() {
    $impl_func "\$@"
}
EOF
}
