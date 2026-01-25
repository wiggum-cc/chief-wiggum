#!/usr/bin/env bash
# =============================================================================
# activity-log.sh - Global JSONL activity log
#
# Provides a structured, append-only activity log for all wiggum events.
# Each line is a JSON object with a timestamp, event type, and context.
#
# Provides:
#   activity_init(project_dir)   - Ensure log directory and file exist
#   activity_log(event, ...)     - Append one JSON line with flock
# =============================================================================

# Prevent double-sourcing
[ -n "${_ACTIVITY_LOG_LOADED:-}" ] && return 0
_ACTIVITY_LOG_LOADED=1

# Global path to the activity log file (set by activity_init)
_ACTIVITY_LOG_FILE=""

# Initialize the activity log
#
# Args:
#   project_dir - Project root directory (contains .ralph/)
#
# Returns: 0 on success
activity_init() {
    local project_dir="$1"
    local log_dir="${RALPH_DIR:-$project_dir/.ralph}/logs"

    mkdir -p "$log_dir"
    _ACTIVITY_LOG_FILE="$log_dir/activity.jsonl"
    touch "$_ACTIVITY_LOG_FILE"
}

# Append one JSON line to the activity log
#
# Uses flock for safe concurrent writes from multiple workers.
#
# Args:
#   event     - Event name (e.g., "step.started", "agent.completed", "worker.spawned")
#   worker_id - Worker identifier (can be empty)
#   task_id   - Task identifier (can be empty)
#   extra_json_fields... - Additional key=value pairs to include in the JSON
#                          (e.g., "step_id=planning" "agent=product.plan-mode")
#
# Returns: 0 on success, 1 if not initialized
activity_log() {
    local event="$1"
    local worker_id="${2:-}"
    local task_id="${3:-}"
    shift 3 2>/dev/null || shift $#

    # Skip if not initialized
    if [ -z "$_ACTIVITY_LOG_FILE" ]; then
        return 0
    fi

    local ts
    ts=$(date -Iseconds)

    # Build JSON with jq, adding extra fields
    local json
    json=$(jq -c -n \
        --arg ts "$ts" \
        --arg event "$event" \
        --arg worker_id "$worker_id" \
        --arg task_id "$task_id" \
        '{ts: $ts, event: $event, worker_id: $worker_id, task_id: $task_id}')

    # Append extra key=value pairs
    local kv
    for kv in "$@"; do
        local key="${kv%%=*}"
        local val="${kv#*=}"
        json=$(echo "$json" | jq -c --arg k "$key" --arg v "$val" '. + {($k): $v}')
    done

    # Atomic append with flock
    (
        flock -w 2 200 || return 0
        echo "$json" >> "$_ACTIVITY_LOG_FILE"
    ) 200>"${_ACTIVITY_LOG_FILE}.lock"
}
