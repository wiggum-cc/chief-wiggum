#!/usr/bin/env bash
# Smart routing - assess task complexity and select pipeline/plan-mode per task
#
# Complexity is inferred from kanban metadata (scope items, acceptance criteria,
# description length) and mapped to pipeline + plan-mode settings:
#
#   LOW    -> fast pipeline, plan mode off
#   MEDIUM -> fast pipeline, plan mode on
#   HIGH   -> default pipeline, plan mode on
set -euo pipefail

[ -n "${_SMART_ROUTING_LOADED:-}" ] && return 0
_SMART_ROUTING_LOADED=1

# Count structured items in a task's kanban entry
#
# Parses the task section to extract scope item count, acceptance criteria
# count, and description word count.
#
# Args:
#   kanban  - Path to kanban file
#   task_id - Task identifier (e.g., TASK-001)
#
# Returns: scope_count|ac_count|desc_words (pipe-delimited)
smart_count_task_items() {
    local kanban="$1"
    local task_id="$2"

    awk -v task="$task_id" '
        $0 ~ "\\*\\*\\[" task "\\]\\*\\*" { found = 1; next }
        !found { next }

        # Stop at next task or section
        found && /^- \[/ { exit }
        found && /^## / { exit }

        # Description field - count words
        found && /^  - Description:/ {
            sub(/^  - Description: */, "")
            desc_words = split($0, _w, /[[:space:]]+/)
            next
        }

        # Section transitions
        found && /^  - Scope:?/ { in_scope = 1; in_ac = 0; next }
        found && /^  - Out of Scope:?/ { in_scope = 0; in_ac = 0; next }
        found && /^  - Acceptance Criteria:?/ { in_scope = 0; in_ac = 1; next }

        # Other top-level fields reset section state
        found && /^  - / && !/^  - (Description|Priority|Dependencies|Scope|Out of Scope|Acceptance Criteria):?/ {
            in_scope = 0; in_ac = 0
        }

        # Count scope items (4-space indented sub-items)
        found && in_scope && /^    - / { scope_count++; next }

        # Count acceptance criteria items
        found && in_ac && /^    - / { ac_count++; next }

        END {
            printf "%d|%d|%d\n", scope_count + 0, ac_count + 0, desc_words + 0
        }
    ' "$kanban"
}

# Assess task complexity from kanban metadata
#
# Heuristic:
#   combined = scope_items + acceptance_criteria
#   combined <= 3  -> low
#   combined <= 7  -> medium
#   combined > 7   -> high
#   Override: description > 100 words bumps low -> medium
#
# Args:
#   kanban  - Path to kanban file
#   task_id - Task identifier
#
# Returns: low, medium, or high
smart_assess_complexity() {
    local kanban="$1"
    local task_id="$2"

    local counts
    counts=$(smart_count_task_items "$kanban" "$task_id")

    local scope_count ac_count desc_words
    IFS='|' read -r scope_count ac_count desc_words <<< "$counts"

    local combined=$(( scope_count + ac_count ))
    local complexity

    if [ "$combined" -le 3 ]; then
        complexity="low"
    elif [ "$combined" -le 7 ]; then
        complexity="medium"
    else
        complexity="high"
    fi

    # Override: long description bumps low -> medium
    if [ "$complexity" = "low" ] && [ "$desc_words" -gt 100 ]; then
        complexity="medium"
    fi

    echo "$complexity"
}

# Map complexity to pipeline and plan-mode settings
#
# Args:
#   complexity - low, medium, or high
#
# Returns: pipeline|plan_mode (pipe-delimited)
#   pipeline is empty string for default pipeline
smart_get_routing() {
    local complexity="$1"

    case "$complexity" in
        low)    echo "fast|false" ;;
        medium) echo "fast|true" ;;
        high)   echo "|true" ;;
        *)      echo "|true" ;;  # Default to high behavior
    esac
}
