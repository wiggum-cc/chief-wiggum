#!/usr/bin/env bash
# process.sh - Safe process management utilities
#
# Provides helpers to avoid common bash pitfalls under set -euo pipefail:
# - wait_safe: Capture exit codes without set -e killing the parent
# - run_capturing_exit: Run command capturing exit code
# - kill_safe: Kill process without errors if already dead
set -euo pipefail

[ -n "${_PROCESS_SH_LOADED:-}" ] && return 0
_PROCESS_SH_LOADED=1

# Safely wait for a process and capture its exit code
#
# Under set -e, bare `wait "$pid"` will kill the calling script if the
# process exited non-zero. This helper captures the exit code safely.
#
# IMPORTANT: Do NOT use exit_code=$(wait_safe "$pid") — the $() subshell
# cannot wait for the parent's background PID and returns 127. Use
# wait_safe_var instead, or redirect to a file.
#
# Args:
#   pid - Process ID to wait for
#
# Returns: Exit code of the waited process (echoed to stdout)
# Exit: Always 0 (to not trigger set -e)
#
# Usage:
#   local exit_code=0
#   wait_safe_var exit_code "$pid"    # preferred
#   # OR
#   wait_safe "$pid" > "$tmpfile"     # file redirection (no subshell)
wait_safe() {
    local pid="$1"
    local exit_code=0
    wait "$pid" 2>/dev/null || exit_code=$?
    echo "$exit_code"
}

# Wait for process and store exit code in named variable
#
# More efficient than command substitution when you already have a variable.
#
# Args:
#   var_name - Name of variable to store exit code
#   pid      - Process ID to wait for
#
# Usage:
#   local exit_code=0
#   wait_safe_var exit_code "$pid"
wait_safe_var() {
    local -n _wait_result="$1"
    local pid="$2"
    _wait_result=0
    wait "$pid" 2>/dev/null || _wait_result=$?
}

# Kill a process safely, ignoring errors if already dead
#
# Args:
#   pid    - Process ID to kill
#   signal - Signal to send (default: TERM)
#
# Returns: 0 always (safe to use in set -e context)
kill_safe() {
    local pid="$1"
    local signal="${2:-TERM}"
    kill "-$signal" "$pid" 2>/dev/null || true
}

# Wait for main process and cleanup watchdog/timeout process
#
# Common pattern: main process with a watchdog. Wait for main,
# then kill and wait for watchdog.
#
# Args:
#   main_pid    - Main process to wait for
#   watchdog_pid - Watchdog/timeout process to cleanup
#
# Returns: Exit code of main process (echoed)
wait_with_watchdog() {
    local main_pid="$1"
    local watchdog_pid="$2"
    local exit_code=0
    
    wait "$main_pid" 2>/dev/null || exit_code=$?
    kill_safe "$watchdog_pid"
    wait "$watchdog_pid" 2>/dev/null || true
    
    echo "$exit_code"
}

# Run a command capturing its exit code without triggering set -e
#
# Args:
#   ... - Command and arguments to run
#
# Outputs:
#   stdout/stderr of command go to normal destinations
#   Exit code echoed to stdout after command completes
#
# Usage:
#   exit_code=$(run_capturing_exit some_command --flag)
run_capturing_exit() {
    local exit_code=0
    "$@" || exit_code=$?
    echo "$exit_code"
}

# Run a command storing exit code in named variable
#
# More efficient for inline use without subshells.
#
# Args:
#   var_name - Name of variable to store exit code
#   ...      - Command and arguments
#
# Usage:
#   local rc=0
#   run_capturing_exit_var rc some_command --flag
run_capturing_exit_var() {
    local -n _run_result="$1"
    shift
    _run_result=0
    "$@" || _run_result=$?
}

# Check if a process is still running
#
# Args:
#   pid - Process ID to check
#
# Returns: 0 if running, 1 if not
is_process_running() {
    local pid="$1"
    kill -0 "$pid" 2>/dev/null
}
