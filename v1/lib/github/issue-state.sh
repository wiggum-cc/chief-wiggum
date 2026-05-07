#!/usr/bin/env bash
# issue-state.sh - Manage GitHub issue sync state
#
# Maintains .ralph/github-sync-state.json which tracks:
#   - Per-issue sync metadata (last status, timestamps, description hash)
#   - Global sync timestamps
#
# State file is written atomically (write tmp + mv) to survive crashes.
set -euo pipefail

# Prevent double-sourcing
[ -n "${_GITHUB_ISSUE_STATE_LOADED:-}" ] && return 0
_GITHUB_ISSUE_STATE_LOADED=1
[ -z "${_WIGGUM_SRC_PLATFORM_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/platform.sh"

# =============================================================================
# State File Paths
# =============================================================================

# Get the path to the sync state file
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: path on stdout
_github_sync_state_file() {
    echo "$1/github-sync-state.json"
}

# =============================================================================
# State File Operations
# =============================================================================

# Initialize the sync state file if it doesn't exist
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: 0 always
github_sync_state_init() {
    local ralph_dir="$1"
    local state_file
    state_file=$(_github_sync_state_file "$ralph_dir")

    if [ ! -s "$state_file" ]; then
        echo '{"version":"2.0","last_down_sync_at":0,"last_up_sync_at":0,"issues":{}}' | \
            jq '.' > "$state_file"
    fi
}

# Load the sync state file
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: JSON content on stdout
github_sync_state_load() {
    local ralph_dir="$1"
    local state_file
    state_file=$(_github_sync_state_file "$ralph_dir")

    if [ -s "$state_file" ]; then
        cat "$state_file"
    else
        echo '{"version":"2.0","last_down_sync_at":0,"last_up_sync_at":0,"issues":{}}'
    fi
}

# Save the sync state file atomically
#
# Uses write-to-tmp + mv pattern to prevent corruption on crash.
#
# Args:
#   ralph_dir  - Path to .ralph directory
#   state_json - JSON string to write
#
# Returns: 0 on success, 1 on failure
github_sync_state_save() {
    local ralph_dir="$1"
    local state_json="$2"
    local state_file
    state_file=$(_github_sync_state_file "$ralph_dir")

    local tmp_file
    tmp_file=$(mktemp "${state_file}.XXXXXX")

    if echo "$state_json" | jq '.' > "$tmp_file" 2>/dev/null && [ -s "$tmp_file" ]; then
        mv "$tmp_file" "$state_file"
        return 0
    else
        rm -f "$tmp_file"
        return 1
    fi
}

# Get a specific task entry from state
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Kanban task ID (e.g., "GH-42")
#
# Returns: JSON object on stdout, or "null" if not found
github_sync_state_get_task() {
    local ralph_dir="$1"
    local task_id="$2"

    local state_file
    state_file=$(_github_sync_state_file "$ralph_dir")

    if [ -f "$state_file" ]; then
        jq -r --arg tid "$task_id" '.issues[$tid] // null' "$state_file" 2>/dev/null || echo "null"
    else
        echo "null"
    fi
}

# Update a specific task entry in the state file
#
# Args:
#   ralph_dir  - Path to .ralph directory
#   task_id    - Kanban task ID (e.g., "GH-42")
#   task_json  - JSON object for this task
#
# Returns: 0 on success, 1 on failure
github_sync_state_set_task() {
    local ralph_dir="$1"
    local task_id="$2"
    local task_json="$3"

    local state
    state=$(github_sync_state_load "$ralph_dir")

    local updated
    updated=$(echo "$state" | jq --arg tid "$task_id" --argjson data "$task_json" \
        '.issues[$tid] = $data') || return 1

    github_sync_state_save "$ralph_dir" "$updated"
}

# Remove a task entry from the state file
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Kanban task ID (e.g., "GH-42")
#
# Returns: 0 on success
github_sync_state_remove_task() {
    local ralph_dir="$1"
    local task_id="$2"

    local state
    state=$(github_sync_state_load "$ralph_dir")

    local updated
    updated=$(echo "$state" | jq --arg tid "$task_id" 'del(.issues[$tid])') || return 1

    github_sync_state_save "$ralph_dir" "$updated"
}

# Update the last down-sync timestamp
#
# Args:
#   ralph_dir - Path to .ralph directory
#   timestamp - Unix epoch seconds (optional, defaults to now)
#
# Returns: 0 on success
github_sync_state_set_down_sync_time() {
    local ralph_dir="$1"
    local timestamp="${2:-$(epoch_now)}"

    local state
    state=$(github_sync_state_load "$ralph_dir")

    local updated
    updated=$(echo "$state" | jq --argjson ts "$timestamp" '.last_down_sync_at = $ts') || return 1

    github_sync_state_save "$ralph_dir" "$updated"
}

# Update the last up-sync timestamp
#
# Args:
#   ralph_dir - Path to .ralph directory
#   timestamp - Unix epoch seconds (optional, defaults to now)
#
# Returns: 0 on success
github_sync_state_set_up_sync_time() {
    local ralph_dir="$1"
    local timestamp="${2:-$(epoch_now)}"

    local state
    state=$(github_sync_state_load "$ralph_dir")

    local updated
    updated=$(echo "$state" | jq --argjson ts "$timestamp" '.last_up_sync_at = $ts') || return 1

    github_sync_state_save "$ralph_dir" "$updated"
}

# Get all tracked task IDs
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: newline-separated task IDs on stdout
github_sync_state_list_tasks() {
    local ralph_dir="$1"

    local state_file
    state_file=$(_github_sync_state_file "$ralph_dir")

    if [ -f "$state_file" ]; then
        jq -r '.issues | keys[]' "$state_file" 2>/dev/null || true
    fi
}

# Find the task ID that tracks a given GitHub issue number
#
# Args:
#   ralph_dir    - Path to .ralph directory
#   issue_number - GitHub issue number (string)
#
# Returns: task ID on stdout, or empty string if not found
github_sync_state_find_task_by_issue() {
    local ralph_dir="$1"
    local issue_number="$2"

    local state_file
    state_file=$(_github_sync_state_file "$ralph_dir")

    if [ -f "$state_file" ]; then
        jq -r --argjson num "$issue_number" \
            '.issues | to_entries[] | select(.value.issue_number == $num) | .key' \
            "$state_file" 2>/dev/null || true
    fi
}

# Create a new issue state entry
#
# Args:
#   issue_number           - GitHub issue number (integer)
#   last_remote_updated_at - ISO 8601 timestamp from GitHub
#   last_synced_status     - Kanban status char (e.g., " ")
#   last_remote_state      - GitHub issue state ("open" or "closed")
#   description_hash       - SHA256 hash of description content
#
# Returns: JSON object on stdout
github_sync_state_create_entry() {
    local issue_number="$1"
    local last_remote_updated_at="$2"
    local last_synced_status="$3"
    local last_remote_state="$4"
    local description_hash="$5"

    jq -n \
        --argjson num "$issue_number" \
        --arg updated "$last_remote_updated_at" \
        --arg status "$last_synced_status" \
        --arg state "$last_remote_state" \
        --arg hash "$description_hash" \
        '{
            issue_number: $num,
            last_remote_updated_at: $updated,
            last_synced_status: $status,
            last_remote_state: $state,
            description_hash: $hash,
            pr_linked: false
        }'
}

# Compute a hash of issue description content for change detection
#
# Args:
#   content - String to hash
#
# Returns: hash string on stdout (sha256:prefix)
github_sync_hash_content() {
    local content="$1"
    local hash
    hash=$(printf '%s' "$content" | sha256sum 2>/dev/null | cut -d' ' -f1 || \
           printf '%s' "$content" | shasum -a 256 2>/dev/null | cut -d' ' -f1 || \
           echo "none")
    echo "sha256:$hash"
}
