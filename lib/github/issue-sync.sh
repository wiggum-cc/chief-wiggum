#!/usr/bin/env bash
# issue-sync.sh - Core GitHub issue sync engine
#
# Two-way sync between GitHub Issues and .ralph/kanban.md:
#   - Down sync (GitHub -> kanban): Creates/updates kanban tasks from issues
#   - Up sync (kanban -> GitHub): Updates issue labels/state from kanban status
#
# Authority model:
#   - Pending tasks [ ]: remote-authoritative (content updates accepted)
#   - In-progress+ [=]/[P]/[x]/[*]/[N]: local-authoritative (content frozen)
set -euo pipefail

# Prevent double-sourcing
[ -n "${_GITHUB_ISSUE_SYNC_LOADED:-}" ] && return 0
_GITHUB_ISSUE_SYNC_LOADED=1

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/github/issue-config.sh"
source "$WIGGUM_HOME/lib/github/issue-state.sh"
source "$WIGGUM_HOME/lib/github/issue-parser.sh"
source "$WIGGUM_HOME/lib/github/issue-writer.sh"

# =============================================================================
# Internal: GitHub API Helpers
# =============================================================================

# Fetch open issues with the gate label
#
# Args:
#   label_filter - Required label name
#
# Returns: JSON array on stdout, "[]" on failure
_github_fetch_open_issues() {
    local label_filter="$1"

    local result exit_code=0
    result=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh issue list \
        --label "$label_filter" \
        --state open \
        --json number,title,body,labels,author,state,updatedAt \
        --limit 100 \
        2>&1) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        if [ "$exit_code" -eq 124 ]; then
            log_error "GitHub issue list timeout"
        else
            log_error "GitHub issue list failed (exit: $exit_code)"
            log_debug "Output: $result"
        fi
        echo "[]"
        return 1
    fi

    echo "$result"
}

# Fetch recently closed issues with the gate label
#
# Args:
#   label_filter - Required label name
#
# Returns: JSON array on stdout, "[]" on failure
_github_fetch_closed_issues() {
    local label_filter="$1"

    local result exit_code=0
    result=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh issue list \
        --label "$label_filter" \
        --state closed \
        --json number,title,state,updatedAt \
        --limit 100 \
        2>&1) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        if [ "$exit_code" -eq 124 ]; then
            log_error "GitHub closed issue list timeout"
        else
            log_error "GitHub closed issue list failed (exit: $exit_code)"
        fi
        echo "[]"
        return 1
    fi

    echo "$result"
}

# =============================================================================
# Internal: Kanban Helpers
# =============================================================================

# Get the current kanban status for a task
#
# Args:
#   kanban_file - Path to kanban.md
#   task_id     - Task ID (e.g., "GH-42")
#
# Returns: status char on stdout (" ", "=", "P", "x", "*", "N"), or empty if not found
_get_kanban_status() {
    local kanban_file="$1"
    local task_id="$2"

    # Use awk to find task and extract status char
    awk -v tid="$task_id" '
        $0 ~ "\\*\\*\\[" tid "\\]\\*\\*" {
            match($0, /\[.\]/)
            print substr($0, RSTART+1, 1)
            exit
        }
    ' "$kanban_file"
}

# Check if a task exists in the kanban
#
# Args:
#   kanban_file - Path to kanban.md
#   task_id     - Task ID
#
# Returns: 0 if exists, 1 if not
_kanban_task_exists() {
    local kanban_file="$1"
    local task_id="$2"

    grep -qF "**[$task_id]**" "$kanban_file" 2>/dev/null
}

# Build extra fields string for add_kanban_task
#
# Args:
#   complexity          - Complexity value (optional)
#   scope               - Scope text (optional)
#   out_of_scope        - Out of scope text (optional)
#   acceptance_criteria  - Acceptance criteria text (optional)
#
# Returns: newline-separated field lines on stdout
_build_extra_fields() {
    local complexity="${1:-}"
    local scope="${2:-}"
    local out_of_scope="${3:-}"
    local acceptance_criteria="${4:-}"
    local result=""

    if [ -n "$complexity" ]; then
        result="Complexity: $complexity"
    fi
    if [ -n "$scope" ]; then
        [ -n "$result" ] && result="$result"$'\n'
        result="${result}Scope: $scope"
    fi
    if [ -n "$out_of_scope" ]; then
        [ -n "$result" ] && result="$result"$'\n'
        result="${result}Out of Scope: $out_of_scope"
    fi
    if [ -n "$acceptance_criteria" ]; then
        [ -n "$result" ] && result="$result"$'\n'
        result="${result}Acceptance Criteria: $acceptance_criteria"
    fi

    echo "$result"
}

# =============================================================================
# Down Sync (GitHub -> Local)
# =============================================================================

# Sync open GitHub issues to local kanban
#
# Args:
#   ralph_dir - Path to .ralph directory
#   dry_run   - "true" to only show planned changes
#
# Returns: 0 on success, 1 on failure
github_issue_sync_down() {
    local ralph_dir="$1"
    local dry_run="${2:-false}"

    local kanban_file="$ralph_dir/kanban.md"
    if [ ! -f "$kanban_file" ]; then
        log_error "Kanban file not found: $kanban_file"
        return 1
    fi

    # Ensure sync state exists
    github_sync_state_init "$ralph_dir"

    local added=0
    local updated=0
    local skipped=0
    local closed_handled=0

    # --- Process OPEN issues ---
    log_debug "Fetching open issues with label '$GITHUB_SYNC_LABEL_FILTER'..."
    local open_issues
    open_issues=$(_github_fetch_open_issues "$GITHUB_SYNC_LABEL_FILTER") || return 1

    local issue_count
    issue_count=$(echo "$open_issues" | jq 'length')
    log_debug "Found $issue_count open issue(s)"

    local i=0
    while [ "$i" -lt "$issue_count" ]; do
        local issue_json
        issue_json=$(echo "$open_issues" | jq ".[$i]")
        ((++i))

        # Parse issue
        local parsed
        parsed=$(github_issue_parse "$issue_json") || {
            ((++skipped))
            continue
        }

        local number task_id brief description priority complexity dependencies
        local scope out_of_scope acceptance_criteria updated_at author_login author_id labels_json
        number=$(echo "$parsed" | jq -r '.number')
        task_id=$(echo "$parsed" | jq -r '.task_id')
        brief=$(echo "$parsed" | jq -r '.brief')
        description=$(echo "$parsed" | jq -r '.description')
        priority=$(echo "$parsed" | jq -r '.priority')
        complexity=$(echo "$parsed" | jq -r '.complexity')
        dependencies=$(echo "$parsed" | jq -r '.dependencies')
        scope=$(echo "$parsed" | jq -r '.scope')
        out_of_scope=$(echo "$parsed" | jq -r '.out_of_scope')
        acceptance_criteria=$(echo "$parsed" | jq -r '.acceptance_criteria')
        updated_at=$(echo "$parsed" | jq -r '.updated_at')
        author_login=$(echo "$parsed" | jq -r '.author_login')
        author_id=$(echo "$parsed" | jq -r '.author_id')
        labels_json=$(echo "$parsed" | jq '.labels')

        # Validate author
        if ! github_sync_is_author_allowed "$author_id" "$author_login"; then
            log_debug "Skipping issue #$number - author '$author_login' not allowed"
            ((++skipped))
            continue
        fi

        # Priority from labels takes precedence over body
        local label_priority
        label_priority=$(github_sync_get_priority_from_labels "$labels_json")
        if [ -n "$label_priority" ]; then
            priority="$label_priority"
        fi
        # Fallback to default if still empty
        priority="${priority:-$GITHUB_SYNC_DEFAULT_PRIORITY}"

        # Check kanban status
        if _kanban_task_exists "$kanban_file" "$task_id"; then
            local current_status
            current_status=$(_get_kanban_status "$kanban_file" "$task_id")

            # Only update pending tasks (remote-authoritative)
            if [ "$current_status" = " " ]; then
                # Check if content changed (compare description hash)
                local existing_entry
                existing_entry=$(github_sync_state_get_issue "$ralph_dir" "$number")
                local new_hash
                new_hash=$(github_sync_hash_content "$description")

                if [ "$existing_entry" != "null" ]; then
                    local old_hash
                    old_hash=$(echo "$existing_entry" | jq -r '.description_hash // ""')
                    local old_updated
                    old_updated=$(echo "$existing_entry" | jq -r '.last_remote_updated_at // ""')

                    if [ "$old_hash" != "$new_hash" ] && [ "$updated_at" != "$old_updated" ]; then
                        if [ "$dry_run" = "true" ]; then
                            echo "[dry-run] Update task $task_id (issue #$number) - content changed"
                        else
                            update_kanban_task_fields "$kanban_file" "$task_id" \
                                "$description" "$priority" "$dependencies" || true
                            log_debug "Updated task $task_id from issue #$number"
                        fi
                        ((++updated))
                    fi
                fi
            else
                log_debug "Task $task_id is $current_status - skipping content update (local-authoritative)"
            fi
        else
            # New task — add to kanban
            if [ "$dry_run" = "true" ]; then
                echo "[dry-run] Add task $task_id (issue #$number): $brief"
            else
                local extra_fields
                extra_fields=$(_build_extra_fields "$complexity" "$scope" "$out_of_scope" "$acceptance_criteria")

                if add_kanban_task "$kanban_file" "$task_id" "$brief" \
                        "$description" "$priority" "$dependencies" "$extra_fields"; then
                    log "Added task $task_id from issue #$number"
                else
                    log_debug "Task $task_id already exists (race condition) - skipping"
                fi
            fi
            ((++added))
        fi

        # Update sync state for this issue
        if [ "$dry_run" != "true" ]; then
            local desc_hash
            desc_hash=$(github_sync_hash_content "$description")
            local entry
            entry=$(github_sync_state_create_entry "$task_id" "$updated_at" " " "open" "$desc_hash")
            github_sync_state_set_issue "$ralph_dir" "$number" "$entry"
        fi
    done

    # --- Process CLOSED issues ---
    log_debug "Fetching closed issues with label '$GITHUB_SYNC_LABEL_FILTER'..."
    local closed_issues
    closed_issues=$(_github_fetch_closed_issues "$GITHUB_SYNC_LABEL_FILTER") || true

    local closed_count
    closed_count=$(echo "$closed_issues" | jq 'length' 2>/dev/null || echo 0)
    log_debug "Found $closed_count closed issue(s)"

    local j=0
    while [ "$j" -lt "$closed_count" ]; do
        local closed_json
        closed_json=$(echo "$closed_issues" | jq ".[$j]")
        ((++j))

        local closed_number
        closed_number=$(echo "$closed_json" | jq -r '.number')

        # Only process issues we're tracking
        local tracked
        tracked=$(github_sync_state_get_issue "$ralph_dir" "$closed_number")
        [ "$tracked" != "null" ] || continue

        local tracked_task_id
        tracked_task_id=$(echo "$tracked" | jq -r '.task_id')

        # Get current kanban status
        local current_status=""
        if _kanban_task_exists "$kanban_file" "$tracked_task_id"; then
            current_status=$(_get_kanban_status "$kanban_file" "$tracked_task_id")
        fi

        # Apply close rules per the authority model
        case "$current_status" in
            " ")
                # Pending task, human closed = won't do
                if [ "$dry_run" = "true" ]; then
                    echo "[dry-run] Mark $tracked_task_id as [N] (issue #$closed_number closed by human)"
                else
                    update_kanban_status "$kanban_file" "$tracked_task_id" "N"
                    log "Marked $tracked_task_id as [N] (issue #$closed_number closed)"
                fi
                ((++closed_handled))
                ;;
            "*")
                # Failed task, human closed = won't retry
                if [ "$dry_run" = "true" ]; then
                    echo "[dry-run] Mark $tracked_task_id as [N] (issue #$closed_number closed, was failed)"
                else
                    update_kanban_status "$kanban_file" "$tracked_task_id" "N"
                    log "Marked $tracked_task_id as [N] (issue #$closed_number closed, was failed)"
                fi
                ((++closed_handled))
                ;;
            *)
                # In-progress, pending-approval, completed, not-planned: no change
                log_debug "Issue #$closed_number closed but task $tracked_task_id is '$current_status' - no change"
                ;;
        esac

        # Update sync state
        if [ "$dry_run" != "true" ]; then
            local updated_entry
            updated_entry=$(echo "$tracked" | jq '.last_remote_state = "closed"')
            github_sync_state_set_issue "$ralph_dir" "$closed_number" "$updated_entry"
        fi
    done

    # Update down-sync timestamp
    if [ "$dry_run" != "true" ]; then
        github_sync_state_set_down_sync_time "$ralph_dir"
    fi

    log "Down-sync: added=$added updated=$updated skipped=$skipped closed_handled=$closed_handled"
}

# =============================================================================
# Up Sync (Local -> GitHub)
# =============================================================================

# Push local kanban status changes to GitHub issues
#
# Args:
#   ralph_dir - Path to .ralph directory
#   dry_run   - "true" to only show planned changes
#
# Returns: 0 on success
github_issue_sync_up() {
    local ralph_dir="$1"
    local dry_run="${2:-false}"

    local kanban_file="$ralph_dir/kanban.md"
    if [ ! -f "$kanban_file" ]; then
        log_error "Kanban file not found: $kanban_file"
        return 1
    fi

    # Ensure sync state exists
    github_sync_state_init "$ralph_dir"

    local synced=0
    local unchanged=0

    # Iterate over all tracked issues
    local issue_numbers
    issue_numbers=$(github_sync_state_list_issues "$ralph_dir")

    while IFS= read -r issue_number; do
        [ -n "$issue_number" ] || continue

        local entry
        entry=$(github_sync_state_get_issue "$ralph_dir" "$issue_number")
        [ "$entry" != "null" ] || continue

        local task_id last_synced_status last_remote_state pr_linked
        task_id=$(echo "$entry" | jq -r '.task_id')
        last_synced_status=$(echo "$entry" | jq -r '.last_synced_status // " "')
        last_remote_state=$(echo "$entry" | jq -r '.last_remote_state // "open"')
        pr_linked=$(echo "$entry" | jq -r '.pr_linked // false')

        # Get current kanban status
        local current_status=""
        if _kanban_task_exists "$kanban_file" "$task_id"; then
            current_status=$(_get_kanban_status "$kanban_file" "$task_id")
        else
            log_debug "Task $task_id not found in kanban - skipping up-sync"
            continue
        fi

        # Skip if status hasn't changed
        if [ "$current_status" = "$last_synced_status" ]; then
            ((++unchanged))
            continue
        fi

        # Perform the update
        github_issue_update_status "$issue_number" "$current_status" "$last_synced_status" \
            "$last_remote_state" "$dry_run"

        # Determine new remote state after our update
        local new_remote_state="$last_remote_state"
        if github_sync_should_close "$current_status"; then
            new_remote_state="closed"
        elif [ "$last_remote_state" = "closed" ] && github_sync_should_close "$last_synced_status"; then
            new_remote_state="open"
        fi

        # Check for PR link
        if [ "$pr_linked" = "false" ] && [ "$dry_run" != "true" ]; then
            # Look for PR URL in worker state
            local worker_dir pr_url=""
            worker_dir=$(find "$ralph_dir/workers" -maxdepth 1 -type d -name "worker-${task_id}-*" 2>/dev/null | head -1)
            if [ -n "$worker_dir" ] && [ -f "$worker_dir/pr_url" ]; then
                pr_url=$(cat "$worker_dir/pr_url" 2>/dev/null || true)
            fi
            if [ -n "$pr_url" ]; then
                github_issue_post_pr_link "$issue_number" "$pr_url"
                pr_linked="true"
            fi
        fi

        # Update sync state
        if [ "$dry_run" != "true" ]; then
            local updated_entry
            updated_entry=$(echo "$entry" | jq \
                --arg status "$current_status" \
                --arg state "$new_remote_state" \
                --arg linked "$pr_linked" \
                '.last_synced_status = $status |
                 .last_remote_state = $state |
                 .pr_linked = ($linked == "true")')
            github_sync_state_set_issue "$ralph_dir" "$issue_number" "$updated_entry"
        fi

        ((++synced))
    done <<< "$issue_numbers"

    # Update up-sync timestamp
    if [ "$dry_run" != "true" ]; then
        github_sync_state_set_up_sync_time "$ralph_dir"
    fi

    log "Up-sync: synced=$synced unchanged=$unchanged"
}

# =============================================================================
# Combined Sync
# =============================================================================

# Run a full sync cycle (down + up)
#
# Args:
#   ralph_dir - Path to .ralph directory
#   dry_run   - "true" to only show planned changes
#
# Returns: 0 on success
github_issue_sync() {
    local ralph_dir="$1"
    local dry_run="${2:-false}"

    log_debug "Starting GitHub issue sync cycle..."

    # Down sync first (new issues -> kanban)
    github_issue_sync_down "$ralph_dir" "$dry_run" || {
        log_error "Down-sync failed"
        return 1
    }

    # Up sync (kanban status -> GitHub)
    github_issue_sync_up "$ralph_dir" "$dry_run" || {
        log_error "Up-sync failed"
        return 1
    }

    log_debug "GitHub issue sync cycle complete"
}

# =============================================================================
# Status Report
# =============================================================================

# Print a summary of sync state
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: 0 always (outputs to stdout)
github_issue_sync_status() {
    local ralph_dir="$1"

    local state_file="$ralph_dir/github-sync-state.json"
    if [ ! -f "$state_file" ]; then
        echo "GitHub issue sync: not initialized (no state file)"
        return 0
    fi

    local state
    state=$(cat "$state_file")

    local version last_down last_up issue_count
    version=$(echo "$state" | jq -r '.version // "unknown"')
    last_down=$(echo "$state" | jq -r '.last_down_sync_at // 0')
    last_up=$(echo "$state" | jq -r '.last_up_sync_at // 0')
    issue_count=$(echo "$state" | jq '.issues | length')

    echo "GitHub Issue Sync Status"
    echo "========================"
    echo "  State version: $version"
    echo "  Tracked issues: $issue_count"

    if [ "$last_down" -gt 0 ]; then
        local down_date
        down_date=$(date -d "@$last_down" -Iseconds 2>/dev/null || date -r "$last_down" -Iseconds 2>/dev/null || echo "epoch:$last_down")
        echo "  Last down-sync: $down_date"
    else
        echo "  Last down-sync: never"
    fi

    if [ "$last_up" -gt 0 ]; then
        local up_date
        up_date=$(date -d "@$last_up" -Iseconds 2>/dev/null || date -r "$last_up" -Iseconds 2>/dev/null || echo "epoch:$last_up")
        echo "  Last up-sync: $up_date"
    else
        echo "  Last up-sync: never"
    fi

    if [ "$issue_count" -gt 0 ]; then
        echo ""
        echo "  Tracked Issues:"
        echo "$state" | jq -r '.issues | to_entries[] | "    #\(.key): \(.value.task_id) (status: \(.value.last_synced_status), remote: \(.value.last_remote_state))"'
    fi
}
