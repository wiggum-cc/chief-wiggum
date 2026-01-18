#!/usr/bin/env bash
# File locking utilities for concurrent worker access

# Log lock contention to metrics
log_lock_wait() {
    local file="$1"
    local wait_time="$2"
    local log_file="${RALPH_DIR:-.ralph}/logs/lock-contention.log"

    # Create log directory if needed
    mkdir -p "$(dirname "$log_file")"

    # Create header if file doesn't exist
    if [ ! -f "$log_file" ]; then
        echo "# File Lock Contention Log" > "$log_file"
        echo "# Format: [timestamp] lock_file | task_id | worker_id | wait_time_seconds" >> "$log_file"
        echo "" >> "$log_file"
    fi

    local timestamp=$(date -Iseconds)
    echo "[$timestamp] $file | task_id=${TASK_ID:-unknown} | worker_id=${WORKER_ID:-unknown} | wait_time=${wait_time}s" >> "$log_file"
}

# Retry a command with file locking
# Usage: with_file_lock <file> <max_retries> <command>
with_file_lock() {
    local file="$1"
    local max_retries="${2:-5}"
    shift 2
    local lock_file="${file}.lock"
    local retry=0
    local start_time=$(date +%s)

    while [ $retry -lt $max_retries ]; do
        # Try to acquire lock with flock
        (
            flock -w 10 200 || exit 1

            # Execute command while holding lock
            "$@"

        ) 200>"$lock_file"

        local result=$?

        if [ $result -eq 0 ]; then
            # Success - log wait time if we had to wait
            local wait_time=$(($(date +%s) - start_time))
            if [ $wait_time -gt 0 ]; then
                log_lock_wait "$file" "$wait_time"
            fi

            # Clean up lock file
            rm -f "$lock_file"
            return 0
        fi

        # Failed - retry after delay
        ((retry++))
        if [ $retry -lt $max_retries ]; then
            sleep $((retry * 2))  # Exponential backoff
        fi
    done

    # All retries failed - log total wait time
    local total_wait=$(($(date +%s) - start_time))
    log_lock_wait "$file" "$total_wait"

    rm -f "$lock_file"
    return 1
}

# Update kanban.md status with locking
# Usage: update_kanban_status <kanban_file> <task_id> <new_status>
# new_status can be: [ ] (pending), [=] (in-progress), [x] (complete)
update_kanban_status() {
    local kanban_file="$1"
    local task_id="$2"
    local new_status="$3"

    # Match any status and replace with new status
    with_file_lock "$kanban_file" 5 \
        sed -i "s/- \[[^\]]*\] \*\*\[$task_id\]\*\*/- [$new_status] **[$task_id]**/" "$kanban_file"
}

# Update kanban.md to mark complete with locking (convenience function)
# Usage: update_kanban <kanban_file> <task_id>
update_kanban() {
    update_kanban_status "$1" "$2" "x"
}

# Update kanban.md to mark failed with locking (convenience function)
# Usage: update_kanban_failed <kanban_file> <task_id>
update_kanban_failed() {
    update_kanban_status "$1" "$2" "*"
}

# Append to changelog.md with locking
# Usage: append_changelog <changelog_file> <task_id> <worker_id> <description> <pr_url> [summary]
append_changelog() {
    local changelog_file="$1"
    local task_id="$2"
    local worker_id="$3"
    local description="$4"
    local pr_url="${5:-N/A}"
    local summary="${6:-}"
    local timestamp=$(date -Iseconds)

    local entry="
## [$task_id] - $timestamp

- **Description**: $description
- **Worker**: $worker_id
- **PR**: $pr_url
- **Status**: Completed
"

    # Add detailed summary if provided
    if [ -n "$summary" ]; then
        entry="${entry}
### Summary

${summary}
"
    fi

    # Use a temporary file to handle multi-line content safely
    local temp_file=$(mktemp)
    echo "$entry" > "$temp_file"

    with_file_lock "$changelog_file" 5 \
        bash -c 'cat "$1" >> "$2"' _ "$temp_file" "$changelog_file"

    rm -f "$temp_file"
}
