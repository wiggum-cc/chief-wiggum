#!/usr/bin/env bash
# worker-pool.sh - Unified worker pool management
#
# Replaces separate active_workers, active_fix_workers, and active_resolve_workers
# arrays with a single unified pool abstraction. Supports three worker types:
#   - main:    Primary task workers
#   - fix:     PR comment fix workers
#   - resolve: Merge conflict resolution workers
#
# Worker entries are stored as: "type|task_id|start_time"
#
# shellcheck disable=SC2034  # Variables are used externally (POOL_CLEANUP_*)
# shellcheck disable=SC2153  # RALPH_DIR is set by caller (documented requirement)
set -euo pipefail

[ -n "${_WORKER_POOL_LOADED:-}" ] && return 0
_WORKER_POOL_LOADED=1

# Pool storage - PID -> "type|task_id|start_time"
declare -gA _WORKER_POOL=()

# Initialize the worker pool (clears any existing state)
pool_init() {
    _WORKER_POOL=()
}

# Add a worker to the pool
#
# Args:
#   pid     - Process ID
#   type    - Worker type (main|fix|resolve)
#   task_id - Task identifier
#
# Returns: 0 on success, 1 if PID already exists
pool_add() {
    local pid="$1"
    local type="$2"
    local task_id="$3"
    local start_time
    start_time=$(date +%s)

    # Validate type
    case "$type" in
        main|fix|resolve) ;;
        *)
            echo "pool_add: invalid type '$type'" >&2
            return 1
            ;;
    esac

    # Check for duplicate
    if [ -n "${_WORKER_POOL[$pid]+x}" ]; then
        return 1
    fi

    _WORKER_POOL[$pid]="$type|$task_id|$start_time"

    # Persist to disk so subshell callers are visible to the main process
    if [ -n "${RALPH_DIR:-}" ]; then
        local pending_file="$RALPH_DIR/.pool-pending"
        (
            flock -x 200
            echo "$pid|$type|$task_id|$start_time" >> "$pending_file"
        ) 200>"$pending_file.lock"
    fi

    return 0
}

# Ingest pending pool entries written to disk by subshells
#
# Reads $ralph_dir/.pool-pending under flock, adds each entry to
# _WORKER_POOL (skipping duplicates), then truncates the file.
#
# Args:
#   ralph_dir - Ralph directory path
pool_ingest_pending() {
    local ralph_dir="$1"
    local pending_file="$ralph_dir/.pool-pending"

    [ -s "$pending_file" ] || return 0

    local lines=""
    {
        flock -x 200
        lines=$(cat "$pending_file")
        : > "$pending_file"
    } 200>"$pending_file.lock"

    local line
    while IFS= read -r line; do
        [ -n "$line" ] || continue
        local pid type task_id start_time
        IFS='|' read -r pid type task_id start_time <<< "$line"
        # Skip if already in pool
        [ -z "${_WORKER_POOL[$pid]+x}" ] || continue
        _WORKER_POOL[$pid]="$type|$task_id|$start_time"
    done <<< "$lines"
}

# Remove a worker from the pool
#
# Args:
#   pid - Process ID
#
# Returns: 0 on success, 1 if not found
pool_remove() {
    local pid="$1"

    if [ -z "${_WORKER_POOL[$pid]+x}" ]; then
        return 1
    fi

    unset "_WORKER_POOL[$pid]"
    return 0
}

# Get worker info from the pool
#
# Args:
#   pid - Process ID
#
# Returns: echoes "type|task_id|start_time" or empty if not found
# Exit: 0 if found, 1 if not found
pool_get() {
    local pid="$1"

    if [ -z "${_WORKER_POOL[$pid]+x}" ]; then
        return 1
    fi

    echo "${_WORKER_POOL[$pid]}"
    return 0
}

# Get worker type from the pool
#
# Args:
#   pid - Process ID
#
# Returns: echoes type (main|fix|resolve) or empty if not found
pool_get_type() {
    local pid="$1"
    local info

    if ! info=$(pool_get "$pid"); then
        return 1
    fi

    echo "${info%%|*}"
}

# Get task_id for a worker
#
# Args:
#   pid - Process ID
#
# Returns: echoes task_id or empty if not found
pool_get_task_id() {
    local pid="$1"
    local info

    if ! info=$(pool_get "$pid"); then
        return 1
    fi

    local rest="${info#*|}"
    echo "${rest%%|*}"
}

# Get start time for a worker
#
# Args:
#   pid - Process ID
#
# Returns: echoes start_time (epoch seconds) or empty if not found
pool_get_start_time() {
    local pid="$1"
    local info

    if ! info=$(pool_get "$pid"); then
        return 1
    fi

    echo "${info##*|}"
}

# Find worker PID by task_id
#
# Args:
#   task_id - Task identifier to search for
#
# Returns: echoes PID if found, empty otherwise
# Exit: 0 if found, 1 if not found
pool_find_by_task() {
    local search_task_id="$1"

    for pid in "${!_WORKER_POOL[@]}"; do
        local info="${_WORKER_POOL[$pid]}"
        local rest="${info#*|}"
        local task_id="${rest%%|*}"
        if [ "$task_id" = "$search_task_id" ]; then
            echo "$pid"
            return 0
        fi
    done

    return 1
}

# Count workers in the pool
#
# Args:
#   type - Optional: filter by type (main|fix|resolve). If omitted, counts all.
#
# Returns: echoes count
pool_count() {
    local filter_type="${1:-}"
    local count=0

    for pid in "${!_WORKER_POOL[@]}"; do
        if [ -z "$filter_type" ]; then
            ((++count))
        else
            local info="${_WORKER_POOL[$pid]}"
            local type="${info%%|*}"
            if [ "$type" = "$filter_type" ]; then
                ((++count))
            fi
        fi
    done

    echo "$count"
}

# Check if pool has capacity for a worker type
#
# Args:
#   type  - Worker type (main|fix|resolve)
#   limit - Maximum allowed for this type
#
# Returns: 0 if has capacity, 1 if at limit
pool_has_capacity() {
    local type="$1"
    local limit="$2"
    local current

    current=$(pool_count "$type")
    [ "$current" -lt "$limit" ]
}

# Iterate over workers with a callback
#
# Args:
#   type     - Worker type filter (main|fix|resolve) or "all"
#   callback - Function name to call with (pid, type, task_id, start_time)
#
# The callback receives:
#   $1 - pid
#   $2 - type
#   $3 - task_id
#   $4 - start_time
pool_foreach() {
    local filter_type="$1"
    local callback="$2"

    for pid in "${!_WORKER_POOL[@]}"; do
        local info="${_WORKER_POOL[$pid]}"
        local type="${info%%|*}"
        local rest="${info#*|}"
        local task_id="${rest%%|*}"
        local start_time="${rest##*|}"

        if [ "$filter_type" = "all" ] || [ "$filter_type" = "$type" ]; then
            "$callback" "$pid" "$type" "$task_id" "$start_time"
        fi
    done
}

# Get all PIDs in the pool
#
# Args:
#   type - Optional: filter by type (main|fix|resolve). If omitted, returns all.
#
# Returns: space-separated list of PIDs
pool_pids() {
    local filter_type="${1:-}"
    local pids=""

    for pid in "${!_WORKER_POOL[@]}"; do
        if [ -z "$filter_type" ]; then
            pids="${pids:+$pids }$pid"
        else
            local info="${_WORKER_POOL[$pid]}"
            local type="${info%%|*}"
            if [ "$type" = "$filter_type" ]; then
                pids="${pids:+$pids }$pid"
            fi
        fi
    done

    echo "$pids"
}

# Check if a task is already in the pool (any type)
#
# Args:
#   task_id - Task identifier to check
#
# Returns: 0 if found, 1 if not found
# Echoes: PID if found
pool_has_task() {
    local needle="$1"

    for pid in "${!_WORKER_POOL[@]}"; do
        local info="${_WORKER_POOL[$pid]}"
        local rest="${info#*|}"
        local task_id="${rest%%|*}"

        if [ "$task_id" = "$needle" ]; then
            echo "$pid"
            return 0
        fi
    done

    return 1
}

# Clean up finished workers and invoke callbacks
#
# Args:
#   type         - Worker type to check (main|fix|resolve) or "all"
#   timeout      - Timeout in seconds (0 = no timeout). Workers exceeding this are killed.
#   on_complete  - Callback function for completed workers: fn(worker_dir, task_id)
#   on_timeout   - Callback function for timed-out workers: fn(worker_dir, task_id)
#
# Requires: RALPH_DIR and find_worker_by_task_id to be available
#
# Returns:
#   Sets POOL_CLEANUP_COUNT to number of workers cleaned up
#   Sets POOL_CLEANUP_EVENT to "true" if any workers were cleaned up
pool_cleanup_finished() {
    local filter_type="$1"
    local timeout="${2:-0}"
    local on_complete="${3:-}"
    local on_timeout="${4:-}"
    local now
    now=$(date +%s)

    POOL_CLEANUP_COUNT=0
    POOL_CLEANUP_EVENT=false

    # Collect PIDs to process (avoid modifying array while iterating)
    local pids_to_check
    pids_to_check=$(pool_pids "$filter_type")

    for pid in $pids_to_check; do
        local info="${_WORKER_POOL[$pid]}"
        local type="${info%%|*}"
        local rest="${info#*|}"
        local task_id="${rest%%|*}"
        local start_time="${rest##*|}"

        if ! kill -0 "$pid" 2>/dev/null; then
            # Worker finished
            POOL_CLEANUP_EVENT=true
            ((++POOL_CLEANUP_COUNT)) || true

            if [ -n "$on_complete" ]; then
                local worker_dir
                worker_dir=$(find_worker_by_task_id "$RALPH_DIR" "$task_id" 2>/dev/null || true)
                if [ -n "$worker_dir" ]; then
                    "$on_complete" "$worker_dir" "$task_id" || true
                fi
            fi

            pool_remove "$pid"

        elif [ "$timeout" -gt 0 ] && [ $((now - start_time)) -ge "$timeout" ]; then
            # Worker timed out
            POOL_CLEANUP_EVENT=true
            ((++POOL_CLEANUP_COUNT)) || true

            # Kill the timed-out worker
            kill "$pid" 2>/dev/null || true

            if [ -n "$on_timeout" ]; then
                local worker_dir
                worker_dir=$(find_worker_by_task_id "$RALPH_DIR" "$task_id" 2>/dev/null || true)
                if [ -n "$worker_dir" ]; then
                    "$on_timeout" "$worker_dir" "$task_id" || true
                fi
            fi

            pool_remove "$pid"
        fi
    done
}

# Restore pool state from existing worker directories
#
# Scans worker directories for running agents and adds them to the pool.
# Used when orchestrator restarts to recover tracking state.
#
# Args:
#   ralph_dir - Ralph directory path
#
# Requires: scan_active_workers from worker-lifecycle.sh
pool_restore_from_workers() {
    local ralph_dir="$1"

    [ -d "$ralph_dir/workers" ] || return 0

    local scan_output
    scan_output=$(scan_active_workers "$ralph_dir") || {
        local scan_rc=$?
        if [ "$scan_rc" -eq 2 ]; then
            log_warn "pool_restore: Worker scan encountered lock contention"
        fi
    }

    while read -r worker_pid task_id _worker_id; do
        [ -n "$worker_pid" ] || continue

        # Determine worker type from worker_id pattern
        local type="main"
        if [[ "$_worker_id" == *"-fix-"* ]]; then
            type="fix"
        elif [[ "$_worker_id" == *"-resolve-"* ]]; then
            type="resolve"
        fi

        # Get worker creation time from directory
        local worker_dir="$ralph_dir/workers/$_worker_id"
        local start_time
        if [ -d "$worker_dir" ]; then
            # Use directory mtime as approximate start time
            start_time=$(stat -c %Y "$worker_dir" 2>/dev/null || date +%s)
        else
            start_time=$(date +%s)
        fi

        # Add to pool (skip if already exists)
        _WORKER_POOL[$worker_pid]="$type|$task_id|$start_time" 2>/dev/null || true
    done <<< "$scan_output"
}

# Dump pool state for debugging
#
# Returns: echoes pool contents as JSON-like output
pool_dump() {
    echo "{"
    local first=true
    for pid in "${!_WORKER_POOL[@]}"; do
        local info="${_WORKER_POOL[$pid]}"
        local type="${info%%|*}"
        local rest="${info#*|}"
        local task_id="${rest%%|*}"
        local start_time="${rest##*|}"

        if [ "$first" = true ]; then
            first=false
        else
            echo ","
        fi
        echo "  \"$pid\": {\"type\": \"$type\", \"task_id\": \"$task_id\", \"start_time\": $start_time}"
    done
    echo "}"
}
