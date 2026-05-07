#!/usr/bin/env bash
# =============================================================================
# task-source-kanban.sh - Local kanban task source adapter
#
# Implements the task-source interface for local kanban.md files.
# Wraps existing task-parser.sh and file-lock.sh functions.
#
# This is the adapter for WIGGUM_TASK_SOURCE_MODE=local (default).
# =============================================================================
set -euo pipefail

[ -n "${_TASK_SOURCE_KANBAN_LOADED:-}" ] && return 0
_TASK_SOURCE_KANBAN_LOADED=1

# Source dependencies
[ -z "${_WIGGUM_SRC_LOGGER_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/logger.sh"
[ -z "${_WIGGUM_SRC_FILE_LOCK_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/tasks/task-parser.sh"

# =============================================================================
# Adapter Initialization
# =============================================================================

# Initialize the kanban adapter
#
# Args:
#   ralph_dir   - Path to .ralph directory
#   project_dir - Path to project directory
#   server_id   - Server ID (unused in local mode)
#
# Returns: 0 on success
_task_source_adapter_init() {
    local ralph_dir="$1"
    # shellcheck disable=SC2034  # Interface parameter, unused in local mode
    local project_dir="$2"
    # shellcheck disable=SC2034  # Interface parameter, unused in local mode
    local server_id="${3:-}"

    # Verify kanban exists
    if [ ! -f "$ralph_dir/kanban.md" ]; then
        log_error "Kanban file not found: $ralph_dir/kanban.md"
        return 1
    fi

    log_debug "Kanban adapter initialized: $ralph_dir/kanban.md"
    return 0
}

# =============================================================================
# Core Interface Implementation
# =============================================================================

# Get all tasks with metadata
#
# Returns: Lines of "task_id|status|priority|dependencies|owner" on stdout
_task_source_kanban_get_all_tasks() {
    local ralph_dir="$1"
    local kanban="$ralph_dir/kanban.md"

    # Use existing parser, add empty owner field (local mode has no owners)
    get_all_tasks_with_metadata "$kanban" | while IFS='|' read -r task_id status priority deps; do
        echo "$task_id|$status|$priority|$deps|"
    done
}

# Claim a task (local mode: no-op, always succeeds for pending tasks)
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Task identifier
#
# Returns: 0 if task is pending and claimable, 1 otherwise
_task_source_kanban_claim_task() {
    local ralph_dir="$1"
    local task_id="$2"
    local kanban="$ralph_dir/kanban.md"

    # In local mode, "claiming" just means verifying the task is pending
    local status
    status=$(get_task_status "$kanban" "$task_id")

    if [ "$status" = " " ]; then
        return 0
    fi

    log_debug "Task $task_id not claimable (status: '$status')"
    return 1
}

# Release a task (local mode: no-op)
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Task identifier
#
# Returns: 0 always
_task_source_kanban_release_task() {
    # No-op in local mode
    return 0
}

# Set task status
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Task identifier
#   status    - New status character
#
# Returns: 0 on success
_task_source_kanban_set_status() {
    local ralph_dir="$1"
    local task_id="$2"
    local status="$3"
    local kanban="$ralph_dir/kanban.md"

    update_kanban_status "$kanban" "$task_id" "$status"
}

# Get task status
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Task identifier
#
# Returns: status character on stdout
_task_source_kanban_get_status() {
    local ralph_dir="$1"
    local task_id="$2"
    local kanban="$ralph_dir/kanban.md"

    get_task_status "$kanban" "$task_id"
}

# Get single task details as JSON
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Task identifier
#
# Returns: JSON object on stdout
_task_source_kanban_get_task() {
    local ralph_dir="$1"
    local task_id="$2"
    local kanban="$ralph_dir/kanban.md"

    # Get metadata from cache
    local metadata
    metadata=$(_get_cached_metadata "$kanban")

    local entry
    entry=$(echo "$metadata" | awk -F'|' -v t="$task_id" '$1 == t { print }')

    if [ -z "$entry" ]; then
        echo "null"
        return 1
    fi

    local status priority deps
    IFS='|' read -r _ status priority deps <<< "$entry"

    # Convert status char to string
    local status_str
    case "$status" in
        " ") status_str="pending" ;;
        "=") status_str="in_progress" ;;
        "P") status_str="pending_approval" ;;
        "x") status_str="complete" ;;
        "*") status_str="failed" ;;
        "N") status_str="not_planned" ;;
        *)   status_str="unknown" ;;
    esac

    # Extract full task description using existing function
    local task_content
    task_content=$(extract_task "$task_id" "$kanban" 2>/dev/null || echo "")

    jq -n \
        --arg task_id "$task_id" \
        --arg status "$status_str" \
        --arg status_char "$status" \
        --arg priority "$priority" \
        --arg dependencies "$deps" \
        --arg description "$task_content" \
        '{
            task_id: $task_id,
            status: $status,
            status_char: $status_char,
            priority: $priority,
            dependencies: $dependencies,
            description: $description,
            owner: null
        }'
}

# Get tasks ready to execute
#
# Args:
#   ralph_dir        - Path to .ralph directory
#   ready_since_file - Path to ready-since tracking file
#   aging_factor     - Aging factor for priority calculation
#   sibling_penalty  - Penalty for sibling tasks in progress
#   plan_bonus       - Bonus for tasks with implementation plans
#   dep_bonus        - Bonus per dependent task
#
# Returns: Lines of "effective_pri|task_id" on stdout
_task_source_kanban_get_ready_tasks() {
    local ralph_dir="$1"
    local ready_since_file="${2:-}"
    local aging_factor="${3:-7}"
    local sibling_penalty="${4:-20000}"
    local plan_bonus="${5:-15000}"
    local dep_bonus="${6:-7000}"
    local kanban="$ralph_dir/kanban.md"

    # Pre-fetch metadata to pass to get_ready_tasks
    local metadata
    metadata=$(_get_cached_metadata "$kanban")

    # Use existing get_ready_tasks with metadata parameter (returns pri|task_id)
    get_ready_tasks "$kanban" "$ready_since_file" "$aging_factor" \
        "$sibling_penalty" "$ralph_dir" "$plan_bonus" "$dep_bonus" "$metadata"
}

# Get blocked tasks (pending but dependencies not satisfied)
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: Lines of task_id on stdout
_task_source_kanban_get_blocked_tasks() {
    local ralph_dir="$1"
    local kanban="$ralph_dir/kanban.md"

    get_blocked_tasks "$kanban"
}

# Check if dependencies are satisfied for a task
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Task identifier
#
# Returns: 0 if satisfied, 1 if not
_task_source_kanban_are_deps_satisfied() {
    local ralph_dir="$1"
    local task_id="$2"
    local kanban="$ralph_dir/kanban.md"

    are_dependencies_satisfied "$kanban" "$task_id"
}

# Get task dependencies
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Task identifier
#
# Returns: comma-separated list of dependency task IDs
_task_source_kanban_get_dependencies() {
    local ralph_dir="$1"
    local task_id="$2"
    local kanban="$ralph_dir/kanban.md"

    get_task_dependencies "$kanban" "$task_id"
}

# Get task priority
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Task identifier
#
# Returns: priority string (CRITICAL|HIGH|MEDIUM|LOW)
_task_source_kanban_get_priority() {
    local ralph_dir="$1"
    local task_id="$2"
    local kanban="$ralph_dir/kanban.md"

    get_task_priority "$kanban" "$task_id"
}

# =============================================================================
# Convenience Functions
# =============================================================================

# Get pending tasks ([ ] status)
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: Lines of task_id on stdout
_task_source_kanban_get_pending() {
    local ralph_dir="$1"
    local kanban="$ralph_dir/kanban.md"

    get_todo_tasks "$kanban"
}

# Get in-progress tasks ([=] status)
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: Lines of task_id on stdout
_task_source_kanban_get_in_progress() {
    local ralph_dir="$1"
    local kanban="$ralph_dir/kanban.md"

    get_in_progress_tasks "$kanban"
}

# Get failed tasks ([*] status)
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: Lines of task_id on stdout
_task_source_kanban_get_failed() {
    local ralph_dir="$1"
    local kanban="$ralph_dir/kanban.md"

    get_failed_tasks "$kanban"
}

# Get completed tasks ([x] status)
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: Lines of task_id on stdout
_task_source_kanban_get_completed() {
    local ralph_dir="$1"
    local kanban="$ralph_dir/kanban.md"

    get_completed_tasks "$kanban"
}

# Detect circular dependencies
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: 0 if no cycles, 1 if cycles detected
#          Outputs "SELF:<task_id>" or "CYCLE:<tasks>" lines on stdout
_task_source_kanban_detect_cycles() {
    local ralph_dir="$1"
    local kanban="$ralph_dir/kanban.md"

    detect_circular_dependencies "$kanban"
}
