#!/usr/bin/env bash
# Track and log resource usage (disk space, worktree sizes, file locks)

# Get disk space usage for a directory in bytes
get_disk_usage() {
    local dir="$1"

    if [ ! -d "$dir" ]; then
        echo "0"
        return 1
    fi

    # Use du to get size in bytes
    # -s: summarize (total only)
    # -b: bytes (not blocks)
    du -sb "$dir" 2>/dev/null | cut -f1
}

# Get available disk space in bytes
get_available_disk_space() {
    local path="${1:-.}"

    # Use df to get available space
    # Read the second line (first is header) and extract the 4th field
    local result=$(df -B1 "$path" 2>/dev/null | while read -r line; do
        # Skip header line
        if [[ "$line" =~ ^Filesystem ]]; then
            continue
        fi
        # Print the 4th field (available space)
        echo "$line" | { read fs size used avail rest; echo "$avail"; }
        break
    done)
    echo "${result:-0}"
}

# Format bytes to human-readable format
format_bytes() {
    local bytes=$1

    if [ -z "$bytes" ] || [ "$bytes" -eq 0 ]; then
        echo "0 B"
        return
    fi

    local units=("B" "KB" "MB" "GB" "TB")
    local unit=0
    local size=$bytes

    while [ "$size" -ge 1024 ] && [ "$unit" -lt 4 ]; do
        size=$((size / 1024))
        unit=$((unit + 1))
    done

    echo "${size} ${units[$unit]}"
}

# Track disk space usage for a worker
track_worker_disk_usage() {
    local worker_dir="$1"
    local worker_id="${2:-unknown}"

    if [ ! -d "$worker_dir" ]; then
        echo "Error: Worker directory not found: $worker_dir" >&2
        return 1
    fi

    local workspace_size=$(get_disk_usage "$worker_dir/workspace")
    local total_size=$(get_disk_usage "$worker_dir")
    local available=$(get_available_disk_space "$worker_dir")

    # Export for use in reporting
    export WORKER_WORKSPACE_SIZE_BYTES=$workspace_size
    export WORKER_TOTAL_SIZE_BYTES=$total_size
    export WORKER_AVAILABLE_DISK_BYTES=$available

    # Human-readable formats
    export WORKER_WORKSPACE_SIZE=$(format_bytes "$workspace_size")
    export WORKER_TOTAL_SIZE=$(format_bytes "$total_size")
    export WORKER_AVAILABLE_DISK=$(format_bytes "$available")

    # Log the metrics
    echo "=== Worker Disk Usage Report ==="
    echo ""
    echo "Worker ID: $worker_id"
    echo "Worker Directory: $worker_dir"
    echo ""
    echo "Disk Usage:"
    echo "  Workspace size: $WORKER_WORKSPACE_SIZE ($workspace_size bytes)"
    echo "  Total worker size: $WORKER_TOTAL_SIZE ($total_size bytes)"
    echo "  Available disk space: $WORKER_AVAILABLE_DISK ($available bytes)"
    echo ""
}

# Get git worktree size
get_worktree_size() {
    local worktree_path="$1"

    if [ ! -d "$worktree_path" ]; then
        echo "0"
        return 1
    fi

    # Get size of worktree including .git directory
    get_disk_usage "$worktree_path"
}

# Track all active worktree sizes
track_all_worktrees() {
    local base_dir="${1:-.ralph/workers}"

    if [ ! -d "$base_dir" ]; then
        echo "No active workers found"
        return 0
    fi

    echo "=== Git Worktree Sizes ==="
    echo ""

    local total_size=0
    local count=0

    for worker_dir in "$base_dir"/worker-*/; do
        if [ ! -d "$worker_dir" ]; then
            continue
        fi

        local workspace="$worker_dir/workspace"
        if [ -d "$workspace" ]; then
            local size=$(get_worktree_size "$workspace")
            local formatted=$(format_bytes "$size")
            local worker_name=$(basename "$worker_dir")

            echo "  $worker_name: $formatted ($size bytes)"

            total_size=$((total_size + size))
            count=$((count + 1))
        fi
    done

    if [ "$count" -eq 0 ]; then
        echo "  No active worktrees found"
    else
        echo ""
        echo "Total worktrees: $count"
        echo "Total size: $(format_bytes $total_size) ($total_size bytes)"
    fi
    echo ""
}

# Check if disk space is sufficient before spawning worker
check_disk_space_preflight() {
    local min_required_bytes="${1:-1073741824}"  # Default: 1GB in bytes
    local path="${2:-.}"

    local available=$(get_available_disk_space "$path")

    if [ -z "$available" ] || [ "$available" -eq 0 ]; then
        echo "Error: Unable to determine available disk space" >&2
        return 1
    fi

    if [ "$available" -lt "$min_required_bytes" ]; then
        local available_formatted=$(format_bytes "$available")
        local required_formatted=$(format_bytes "$min_required_bytes")

        echo "WARNING: Low disk space!" >&2
        echo "  Available: $available_formatted" >&2
        echo "  Required: $required_formatted" >&2
        echo "  Shortfall: $(format_bytes $((min_required_bytes - available)))" >&2

        return 2  # Return 2 to indicate warning (not a hard failure)
    fi

    return 0
}

# Log file lock contention
log_lock_contention() {
    local lock_file="$1"
    local wait_time_seconds="$2"
    local task_id="${3:-unknown}"
    local worker_id="${4:-unknown}"

    local timestamp=$(date -Iseconds)
    local log_file="${RALPH_DIR:-.ralph}/logs/lock-contention.log"

    # Create log directory if needed
    mkdir -p "$(dirname "$log_file")"

    # Create header if file doesn't exist
    if [ ! -f "$log_file" ]; then
        echo "# File Lock Contention Log" > "$log_file"
        echo "# Format: [timestamp] lock_file | task_id | worker_id | wait_time_seconds" >> "$log_file"
        echo "" >> "$log_file"
    fi

    # Log the contention event
    echo "[$timestamp] $lock_file | task_id=$task_id | worker_id=$worker_id | wait_time=${wait_time_seconds}s" >> "$log_file"
}

# Report resource usage summary
report_resource_usage() {
    local worker_dir="$1"
    local worker_id="${2:-unknown}"

    echo "=== Resource Usage Summary ==="
    echo ""

    # Track disk usage
    if [ -n "$worker_dir" ] && [ -d "$worker_dir" ]; then
        track_worker_disk_usage "$worker_dir" "$worker_id"
    fi

    # Show lock contention if any
    local lock_log="${RALPH_DIR:-.ralph}/logs/lock-contention.log"
    if [ -f "$lock_log" ]; then
        local contention_count=$(grep -c "worker_id=$worker_id" "$lock_log" 2>/dev/null || echo "0")
        if [ "$contention_count" -gt 0 ]; then
            echo "Lock Contention Events: $contention_count"
            echo "  (See $lock_log for details)"
            echo ""
        fi
    fi
}

# If called directly
if [ $# -gt 0 ]; then
    case "$1" in
        track-worker)
            track_worker_disk_usage "$2" "$3"
            ;;
        track-worktrees)
            track_all_worktrees "$2"
            ;;
        check-disk)
            check_disk_space_preflight "$2" "$3"
            ;;
        report)
            report_resource_usage "$2" "$3"
            ;;
        *)
            echo "Usage: $0 {track-worker|track-worktrees|check-disk|report} [args...]"
            exit 1
            ;;
    esac
fi
