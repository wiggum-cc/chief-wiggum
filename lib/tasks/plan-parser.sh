#!/usr/bin/env bash
# Plan parser for extracting Critical Files from implementation plans
set -euo pipefail

# Parse Critical Files section from a plan file
# Returns files with CREATE or MODIFY actions (not REFERENCE)
# Args: plan_file
# Output: one file path per line (sorted, unique)
get_plan_critical_files() {
    local plan_file="$1"

    [ -f "$plan_file" ] || return 0

    awk '
        /^### Critical Files/ { in_section = 1; next }
        in_section && /^##/ { in_section = 0 }
        in_section {
            # Match table rows with CREATE or MODIFY action
            # Format: | File | Action | Reason |
            if (/^\| .+ \| (CREATE|MODIFY) \|/) {
                # Extract first column (File)
                split($0, cols, "|")
                gsub(/^[ \t]+|[ \t]+$/, "", cols[2])
                if (cols[2] != "" && cols[2] != "File") {
                    print cols[2]
                }
            }
        }
    ' "$plan_file" | sort -u
}

# Get all critical files for a task (looks up plan by task ID)
# Args: ralph_dir task_id
# Output: one file path per line (sorted, unique)
get_task_critical_files() {
    local ralph_dir="$1"
    local task_id="$2"
    local plan_file="$ralph_dir/plans/${task_id}.md"

    if [ -f "$plan_file" ]; then
        get_plan_critical_files "$plan_file"
    fi
}
