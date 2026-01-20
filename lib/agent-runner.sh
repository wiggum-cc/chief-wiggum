#!/usr/bin/env bash
# agent-runner.sh - Generic agent lifecycle management
#
# Provides common functionality for all agent types:
# - PID recording in agent.pid
# - Workspace violation detection
# - Signal handling for graceful shutdown
# - Logging setup
#
# Usage:
#   source "$WIGGUM_HOME/lib/agent-runner.sh"
#   agent_runner_init "$agent_dir" "$project_dir"
#   # ... run your agent logic ...
#   agent_runner_cleanup

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/defaults.sh"
source "$SCRIPT_DIR/logger.sh"
source "$SCRIPT_DIR/violation-monitor.sh"

# Global state for agent runner
_AGENT_RUNNER_DIR=""
_AGENT_RUNNER_PROJECT_DIR=""
_AGENT_RUNNER_INTERRUPTED=false
_AGENT_RUNNER_CHILD_PID=""

# Initialize agent runner
#
# Sets up:
# - PID file (agent.pid)
# - Log file reference
# - Violation monitoring
# - Signal handlers
#
# Args:
#   agent_dir    - Directory for this agent instance (e.g., .ralph/workers/worker-TASK-001-xxx)
#   project_dir  - Project root directory
#   monitor_interval - Violation monitor interval in seconds (default: 30, 0 to disable)
#
# Returns: 0 on success, 1 on failure
agent_runner_init() {
    local agent_dir="$1"
    local project_dir="$2"
    local monitor_interval="${3:-30}"

    if [ -z "$agent_dir" ] || [ -z "$project_dir" ]; then
        log_error "agent_runner_init: agent_dir and project_dir are required"
        return 1
    fi

    _AGENT_RUNNER_DIR="$agent_dir"
    _AGENT_RUNNER_PROJECT_DIR="$project_dir"
    _AGENT_RUNNER_INTERRUPTED=false

    # Ensure agent directory exists
    mkdir -p "$agent_dir"

    # Record PID
    echo "$$" > "$agent_dir/agent.pid"
    log_debug "Agent PID $$ recorded in $agent_dir/agent.pid"

    # Setup signal handlers
    trap '_agent_runner_signal_handler' INT TERM

    # Start violation monitoring if interval > 0
    if [ "$monitor_interval" -gt 0 ]; then
        start_violation_monitor "$project_dir" "$agent_dir" "$monitor_interval"
    fi

    return 0
}

# Internal signal handler
_agent_runner_signal_handler() {
    log "Agent received shutdown signal"
    _AGENT_RUNNER_INTERRUPTED=true

    # Kill child process if running
    if [ -n "$_AGENT_RUNNER_CHILD_PID" ] && kill -0 "$_AGENT_RUNNER_CHILD_PID" 2>/dev/null; then
        log "Terminating child process (PID: $_AGENT_RUNNER_CHILD_PID)"
        kill -TERM "$_AGENT_RUNNER_CHILD_PID" 2>/dev/null || true
        wait "$_AGENT_RUNNER_CHILD_PID" 2>/dev/null || true
    fi
}

# Register a child process for signal handling
#
# Args:
#   child_pid - PID of the child process to track
agent_runner_register_child() {
    _AGENT_RUNNER_CHILD_PID="$1"
}

# Check if shutdown was requested
#
# Returns: 0 if interrupted, 1 if not
agent_runner_interrupted() {
    [ "$_AGENT_RUNNER_INTERRUPTED" = true ]
}

# Detect workspace violations
#
# Checks if any files outside the workspace were modified in project root.
# This is the same check as in worker.sh but exposed as a reusable function.
#
# Args:
#   workspace   - The workspace directory (where agent should work)
#   project_dir - The project root directory (optional, uses init value)
#
# Returns: 0 if no violations, 1 if violations detected
agent_runner_detect_violations() {
    local workspace="$1"
    local project_dir="${2:-$_AGENT_RUNNER_PROJECT_DIR}"

    log_debug "Checking for workspace boundary violations"

    # Check if any files outside workspace were modified in project root
    cd "$project_dir" || return 0

    # Get list of modified files in project root (excluding .ralph directory)
    local modified_files=$(git status --porcelain 2>/dev/null | grep -v "^.. .ralph/" | awk '{print $2}')

    if [[ -n "$modified_files" ]]; then
        log_error "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        log_error "⚠️  CRITICAL: Workspace boundary violation detected!"
        log_error "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        log_error ""
        log_error "Modified files outside workspace:"
        echo "$modified_files" | while read -r file; do
            log_error "  - $file"
        done
        log_error ""
        log_error "Expected workspace: $workspace"
        log_error "Actual modifications: $project_dir"
        log_error ""

        # Create violations log directory if it doesn't exist
        mkdir -p "$project_dir/.ralph/logs"

        # Log violation with timestamp
        {
            echo "================================================================================"
            echo "VIOLATION: Workspace Escape"
            echo "Timestamp: $(date -Iseconds)"
            echo "Agent Dir: $_AGENT_RUNNER_DIR"
            echo "Files modified outside workspace:"
            echo "$modified_files"
            echo "================================================================================"
            echo ""
        } >> "$project_dir/.ralph/logs/violations.log"

        return 1
    fi

    log_debug "No workspace violations detected"
    return 0
}

# Check if violation flag was set by monitor
#
# Returns: 0 if violation detected, 1 otherwise
agent_runner_has_violation_flag() {
    has_violation "$_AGENT_RUNNER_DIR"
}

# Cleanup agent runner
#
# Stops violation monitor and removes PID file.
# Should be called when agent completes or on exit.
agent_runner_cleanup() {
    log_debug "Agent runner cleanup"

    # Stop violation monitor
    stop_violation_monitor

    # Remove PID file
    if [ -n "$_AGENT_RUNNER_DIR" ] && [ -f "$_AGENT_RUNNER_DIR/agent.pid" ]; then
        rm -f "$_AGENT_RUNNER_DIR/agent.pid"
        log_debug "Removed agent PID file"
    fi

    # Clear state
    _AGENT_RUNNER_DIR=""
    _AGENT_RUNNER_PROJECT_DIR=""
    _AGENT_RUNNER_CHILD_PID=""
}

# Get the agent directory
agent_runner_get_dir() {
    echo "$_AGENT_RUNNER_DIR"
}

# Get the project directory
agent_runner_get_project_dir() {
    echo "$_AGENT_RUNNER_PROJECT_DIR"
}
