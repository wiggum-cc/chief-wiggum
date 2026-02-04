#!/usr/bin/env bash
# pr-labels.sh - Manage status labels on GitHub Pull Requests
#
# Mirrors the issue label workflow (issue-writer.sh) for PRs.
# Uses the same status_labels configuration from issue-config.sh.
set -euo pipefail

# Prevent double-sourcing
[ -n "${_GITHUB_PR_LABELS_LOADED:-}" ] && return 0
_GITHUB_PR_LABELS_LOADED=1

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/github/issue-config.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"

# =============================================================================
# Label Management
# =============================================================================

# Add a label to a GitHub PR
#
# Args:
#   pr_number - GitHub PR number
#   label     - Label name to add
#
# Returns: 0 on success, 1 on failure
github_pr_add_label() {
    local pr_number="$1"
    local label="$2"

    local exit_code=0
    timeout "${WIGGUM_GH_TIMEOUT:-30}" gh pr edit "$pr_number" \
        --add-label "$label" >/dev/null 2>&1 || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_warn "Failed to add label '$label' to PR #$pr_number (exit: $exit_code)"
        return 1
    fi
    return 0
}

# Remove a label from a GitHub PR
#
# Args:
#   pr_number - GitHub PR number
#   label     - Label name to remove
#
# Returns: 0 always (removal failure is non-critical)
github_pr_remove_label() {
    local pr_number="$1"
    local label="$2"

    local exit_code=0
    timeout "${WIGGUM_GH_TIMEOUT:-30}" gh pr edit "$pr_number" \
        --remove-label "$label" >/dev/null 2>&1 || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_debug "Could not remove label '$label' from PR #$pr_number (may not exist)"
    fi
    return 0
}

# Remove old status label and add the new one on a PR
#
# Status labels are mutually exclusive. This removes any existing status
# label before adding the new one.
#
# Args:
#   pr_number - GitHub PR number
#   new_label - New status label to set (empty = remove all status labels)
#   old_label - Previous status label to remove (empty = skip removal)
#
# Returns: 0 on success
github_pr_set_status_label() {
    local pr_number="$1"
    local new_label="${2:-}"
    local old_label="${3:-}"

    # Remove old status label if present and different from new
    if [ -n "$old_label" ] && [ "$old_label" != "$new_label" ]; then
        github_pr_remove_label "$pr_number" "$old_label"
    fi

    # Add new status label if present
    if [ -n "$new_label" ]; then
        github_pr_add_label "$pr_number" "$new_label"
    fi
}

# =============================================================================
# High-Level Status Sync
# =============================================================================

# Update the status label on the PR linked to a task
#
# Looks up the PR number from the worker's git-state.json, then applies
# the appropriate status label. No-op if no worker or PR exists.
#
# Args:
#   ralph_dir  - Path to .ralph directory
#   task_id    - Kanban task ID (e.g., "TASK-001")
#   new_status - New kanban status char (e.g., "P", "*")
#   old_status - Previous kanban status char (optional, for label removal)
#
# Returns: 0 always (failures are logged, not fatal)
github_pr_sync_task_status() {
    local ralph_dir="$1"
    local task_id="$2"
    local new_status="$3"
    local old_status="${4:-}"

    # Ensure config is loaded (needed for label mappings)
    [ -n "${GITHUB_SYNC_STATUS_LABELS:-}" ] || load_github_sync_config

    # Find worker directory for this task
    local worker_dir
    worker_dir=$(find_worker_by_task_id "$ralph_dir" "$task_id" 2>/dev/null) || true

    if [ -z "$worker_dir" ] || [ ! -d "$worker_dir" ]; then
        log_debug "github_pr_sync_task_status: no worker for $task_id"
        return 0
    fi

    # Get PR number from git-state.json
    local pr_number
    pr_number=$(git_state_get_pr "$worker_dir")

    if [ -z "$pr_number" ] || [ "$pr_number" = "null" ]; then
        log_debug "github_pr_sync_task_status: no PR for $task_id"
        return 0
    fi

    # Map status chars to labels
    local new_label old_label=""
    new_label=$(github_sync_get_status_label "$new_status")
    if [ -n "$old_status" ]; then
        old_label=$(github_sync_get_status_label "$old_status")
    fi

    # Apply label change
    github_pr_set_status_label "$pr_number" "$new_label" "$old_label"

    log_debug "PR #$pr_number: label set to '${new_label:-<none>}' for task $task_id"
}
