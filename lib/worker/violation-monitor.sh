#!/usr/bin/env bash
# violation-monitor.sh - Background monitor for workspace boundary violations
#
# Monitors iteration logs in real-time (100ms intervals) for violations:
# - Edit tool calls with file_path outside workspace directory
# - Bash commands that operate on git main repo
#
# On violation: immediately terminates agent and creates violation flag.

source "$WIGGUM_HOME/lib/core/logger.sh"

# Global variable for violation monitor PID (needed for cleanup from signal handler)
VIOLATION_MONITOR_PID=""

# Start real-time violation monitor
#
# Args:
#   workspace       - The allowed workspace directory
#   worker_dir      - Worker directory (for logs and violation flag)
#   agent_pid       - PID of the agent to kill on violation
#   project_dir     - The main project directory (for detecting git commands there)
#
# Returns: The PID of the background monitor process (also sets VIOLATION_MONITOR_PID)
start_violation_monitor() {
    local workspace="$1"
    local worker_dir="$2"
    local agent_pid="$3"
    local project_dir="$4"

    local logs_dir="$worker_dir/logs"
    local monitor_log="$worker_dir/violation-monitor.log"

    (
        local last_size=0
        local current_log=""
        local iteration=0

        while kill -0 "$agent_pid" 2>/dev/null; do
            sleep 0.1

            # Find the current iteration log file
            local new_log
            new_log=$(ls -t "$logs_dir"/iteration-*.log 2>/dev/null | head -1)

            # If log file changed, reset position
            if [[ "$new_log" != "$current_log" ]]; then
                current_log="$new_log"
                last_size=0
                ((iteration++)) || true
            fi

            # Skip if no log file yet
            [[ -z "$current_log" ]] && continue
            [[ ! -f "$current_log" ]] && continue

            # Get current file size
            local current_size
            current_size=$(stat -c%s "$current_log" 2>/dev/null || echo 0)

            # Skip if no new content
            [[ "$current_size" -le "$last_size" ]] && continue

            # Read new content and check for violations
            local new_content
            new_content=$(tail -c +$((last_size + 1)) "$current_log" 2>/dev/null)
            last_size=$current_size

            # Parse each line of new content
            while IFS= read -r line; do
                [[ -z "$line" ]] && continue

                # Check for Edit tool violations
                if echo "$line" | grep -q '"name":"Edit"'; then
                    local file_path
                    file_path=$(echo "$line" | grep -oP '"file_path"\s*:\s*"\K[^"]+' 2>/dev/null || true)

                    if [[ -n "$file_path" ]]; then
                        # Allow: workspace paths and ../prd.md
                        if [[ "$file_path" != "$workspace"* ]] && \
                           [[ "$file_path" != "../prd.md" ]] && \
                           [[ "$file_path" != "$worker_dir/prd.md" ]]; then
                            # VIOLATION: Edit outside workspace
                            _log_violation "$monitor_log" "Edit" "$file_path" "$workspace"
                            _create_violation_flag "$worker_dir" "EDIT_OUTSIDE_WORKSPACE" "$file_path"
                            _terminate_agent "$agent_pid" "$worker_dir"
                            exit 1
                        fi
                    fi
                fi

                # Check for Write tool violations
                if echo "$line" | grep -q '"name":"Write"'; then
                    local file_path
                    file_path=$(echo "$line" | grep -oP '"file_path"\s*:\s*"\K[^"]+' 2>/dev/null || true)

                    if [[ -n "$file_path" ]]; then
                        if [[ "$file_path" != "$workspace"* ]] && \
                           [[ "$file_path" != "../prd.md" ]] && \
                           [[ "$file_path" != "$worker_dir/prd.md" ]]; then
                            # VIOLATION: Write outside workspace
                            _log_violation "$monitor_log" "Write" "$file_path" "$workspace"
                            _create_violation_flag "$worker_dir" "WRITE_OUTSIDE_WORKSPACE" "$file_path"
                            _terminate_agent "$agent_pid" "$worker_dir"
                            exit 1
                        fi
                    fi
                fi

                # Check for Bash commands that operate on main repo
                if echo "$line" | grep -q '"name":"Bash"'; then
                    local command
                    command=$(echo "$line" | grep -oP '"command"\s*:\s*"\K[^"]+' 2>/dev/null || true)

                    if [[ -n "$command" ]]; then
                        # Decode JSON escape sequences
                        command=$(echo -e "$command")

                        # Check for git commands in project_dir (not workspace)
                        if echo "$command" | grep -qE "cd\s+['\"]?$project_dir" || \
                           echo "$command" | grep -qE "git\s+(add|commit|push|checkout|branch|merge|rebase|reset)" | grep -v "$workspace"; then
                            # Check if command explicitly targets main repo
                            if [[ "$command" == *"$project_dir"* ]] && [[ "$command" != *"$workspace"* ]]; then
                                # VIOLATION: Git command on main repo
                                _log_violation "$monitor_log" "Bash/Git" "$command" "$workspace"
                                _create_violation_flag "$worker_dir" "GIT_COMMAND_ON_MAIN_REPO" "$command"
                                _terminate_agent "$agent_pid" "$worker_dir"
                                exit 1
                            fi
                        fi
                    fi
                fi

            done <<< "$new_content"
        done
    ) &

    VIOLATION_MONITOR_PID=$!
    log_debug "Violation monitor started with PID: $VIOLATION_MONITOR_PID (watching agent PID: $agent_pid)"
    echo "$VIOLATION_MONITOR_PID"
}

# Internal: Log a violation
_log_violation() {
    local log_file="$1"
    local tool="$2"
    local target="$3"
    local workspace="$4"
    local timestamp
    timestamp=$(date -Iseconds)

    {
        echo "[$timestamp] VIOLATION DETECTED"
        echo "Tool: $tool"
        echo "Target: $target"
        echo "Allowed workspace: $workspace"
        echo "---"
    } >> "$log_file" 2>/dev/null || true

    echo "[VIOLATION MONITOR] $tool violation detected: $target" >&2
}

# Internal: Create violation flag file
_create_violation_flag() {
    local worker_dir="$1"
    local violation_type="$2"
    local details="$3"
    local timestamp
    timestamp=$(date -Iseconds)

    {
        echo "VIOLATION_DETECTED"
        echo "$timestamp"
        echo "Type: $violation_type"
        echo "Details: $details"
    } > "$worker_dir/violation_flag.txt" 2>/dev/null || true
}

# Internal: Terminate the agent process
_terminate_agent() {
    local agent_pid="$1"
    local worker_dir="$2"

    echo "[VIOLATION MONITOR] Terminating agent (PID: $agent_pid) due to violation" >&2

    # Try graceful termination first
    kill -TERM "$agent_pid" 2>/dev/null || true
    sleep 0.5

    # Force kill if still running
    if kill -0 "$agent_pid" 2>/dev/null; then
        kill -9 "$agent_pid" 2>/dev/null || true
    fi
}

# Stop the violation monitor
#
# Args:
#   monitor_pid - The PID of the monitor to stop (optional, uses VIOLATION_MONITOR_PID if not provided)
stop_violation_monitor() {
    local monitor_pid="${1:-$VIOLATION_MONITOR_PID}"

    if [[ -n "$monitor_pid" ]] && kill -0 "$monitor_pid" 2>/dev/null; then
        kill "$monitor_pid" 2>/dev/null || true
        wait "$monitor_pid" 2>/dev/null || true
        log_debug "Violation monitor stopped (PID: $monitor_pid)"
    fi

    # Clear global if we stopped it
    if [[ "$monitor_pid" == "$VIOLATION_MONITOR_PID" ]]; then
        VIOLATION_MONITOR_PID=""
    fi
}

# Check if a violation has been detected
#
# Args:
#   worker_dir - Worker directory to check
#
# Returns: 0 if violation detected, 1 otherwise
has_violation() {
    local worker_dir="$1"
    [[ -f "$worker_dir/violation_flag.txt" ]]
}
