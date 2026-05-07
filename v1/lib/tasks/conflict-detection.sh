#!/usr/bin/env bash
# Conflict detection for file-level task conflicts
# Requires bash 4.3+ for nameref support
set -euo pipefail

# Source plan parser if not already loaded
if ! declare -f get_task_critical_files >/dev/null 2>&1; then
    source "${BASH_SOURCE%/*}/plan-parser.sh"
fi

# Check if a task's critical files overlap with active workers
# Returns 0 if conflict exists, 1 if safe to spawn
# Args: ralph_dir task_id active_workers_array_name
has_file_conflict() {
    local ralph_dir="$1"
    local task_id="$2"
    local -n active_workers_ref="$3"  # nameref to active_workers array

    local task_files
    task_files=$(get_task_critical_files "$ralph_dir" "$task_id")

    # No plan or no critical files = no conflict detection possible (graceful degradation)
    [ -z "$task_files" ] && return 1

    for worker_pid in "${!active_workers_ref[@]}"; do
        local worker_task="${active_workers_ref[$worker_pid]}"

        # Skip self (task that was just spawned checking against itself)
        [ "$worker_task" = "$task_id" ] && continue

        local worker_files
        worker_files=$(get_task_critical_files "$ralph_dir" "$worker_task")

        # Skip workers without critical files
        [ -z "$worker_files" ] && continue

        # Check for intersection using comm
        local overlap
        overlap=$(comm -12 <(echo "$task_files") <(echo "$worker_files"))
        if [ -n "$overlap" ]; then
            return 0  # Conflict found
        fi
    done

    return 1  # No conflict
}

# Get list of conflicting files between task and active workers
# Args: ralph_dir task_id active_workers_array_name
# Output: conflicting file paths (one per line)
get_conflicting_files() {
    local ralph_dir="$1"
    local task_id="$2"
    local -n active_workers_ref="$3"  # nameref to active_workers array

    local task_files
    task_files=$(get_task_critical_files "$ralph_dir" "$task_id")

    [ -z "$task_files" ] && return 0

    local all_conflicts=""

    for worker_pid in "${!active_workers_ref[@]}"; do
        local worker_task="${active_workers_ref[$worker_pid]}"

        # Skip self (task that was just spawned checking against itself)
        [ "$worker_task" = "$task_id" ] && continue

        local worker_files
        worker_files=$(get_task_critical_files "$ralph_dir" "$worker_task")

        [ -z "$worker_files" ] && continue

        # Find intersection
        local overlap
        overlap=$(comm -12 <(echo "$task_files") <(echo "$worker_files"))
        if [ -n "$overlap" ]; then
            all_conflicts="${all_conflicts}${overlap}"$'\n'
        fi
    done

    # Return unique conflicts
    echo "$all_conflicts" | sort -u | grep -v '^$' || true
}

# Get the task ID(s) that conflict with the given task
# Args: ralph_dir task_id active_workers_array_name
# Output: conflicting task IDs (one per line)
get_conflicting_tasks() {
    local ralph_dir="$1"
    local task_id="$2"
    local -n active_workers_ref="$3"  # nameref to active_workers array

    local task_files
    task_files=$(get_task_critical_files "$ralph_dir" "$task_id")

    [ -z "$task_files" ] && return 0

    for worker_pid in "${!active_workers_ref[@]}"; do
        local worker_task="${active_workers_ref[$worker_pid]}"

        # Skip self (task that was just spawned checking against itself)
        [ "$worker_task" = "$task_id" ] && continue

        local worker_files
        worker_files=$(get_task_critical_files "$ralph_dir" "$worker_task")

        [ -z "$worker_files" ] && continue

        # Check for intersection
        local overlap
        overlap=$(comm -12 <(echo "$task_files") <(echo "$worker_files"))
        if [ -n "$overlap" ]; then
            echo "$worker_task"
        fi
    done
}
