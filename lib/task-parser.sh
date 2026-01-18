#!/usr/bin/env bash
# Task parser for markdown kanban and PRD files

has_incomplete_tasks() {
    local file="$1"
    grep -q -- '- \[ \]' "$file"
}

get_todo_tasks() {
    local kanban="$1"
    # Extract task IDs from TASKS section - ONLY incomplete tasks (- [ ])
    awk 'BEGIN{in_tasks=0}
        /^## TASKS$/{in_tasks=1; next}
        /^## / && in_tasks{in_tasks=0}
        in_tasks && /^- \[ \] \*\*\[[A-Za-z]{2,8}-[0-9]+\]\*\*/{
            match($0, /\[[A-Za-z]{2,8}-[0-9]+\]/)
            print substr($0, RSTART+1, RLENGTH-2)
        }' "$kanban"
}

extract_task() {
    local task_id="$1"
    local kanban="$2"

    # Extract task details and create a PRD for worker
    cat <<EOF
# Task: $task_id

$(awk -v task="$task_id" '
    /\*\*\['"$task_id"'\]\*\*/ {found=1; next}
    found && /^  - Description:/ {sub(/^  - Description: /, ""); desc=$0}
    found && /^  - Priority:/ {sub(/^  - Priority: /, ""); priority=$0}
    found && /^  - Dependencies:/ {sub(/^  - Dependencies: /, ""); deps=$0}
    found && /^- \[/ {exit}
    found && /^## / {exit}
    END {
        if (desc) print "## Description\n" desc "\n"
        if (priority) print "## Priority\n" priority "\n"
        if (deps && deps != "none") print "## Dependencies\n" deps "\n"
    }
' "$kanban")

## Checklist

- [ ] Complete the task as described
- [ ] Test the implementation
- [ ] Mark this PRD as complete
EOF
}
