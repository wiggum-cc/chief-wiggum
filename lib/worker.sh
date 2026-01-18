#!/usr/bin/env bash
# Worker script - spawned by wiggum for each task

WORKER_DIR="$1"         # e.g., .ralph/workers/worker-TASK-001-12345
PROJECT_DIR="$2"        # Project root directory
WIGGUM_HOME="${WIGGUM_HOME:-$HOME/.claude/chief-wiggum}"

# Configuration for ralph loop
MAX_ITERATIONS="${WIGGUM_MAX_ITERATIONS:-10}"           # Max outer loop iterations
MAX_TURNS_PER_SESSION="${WIGGUM_MAX_TURNS:-20}"         # Max turns per Claude session (controls context window)

source "$WIGGUM_HOME/lib/ralph-loop.sh"
source "$WIGGUM_HOME/lib/logger.sh"
source "$WIGGUM_HOME/lib/file-lock.sh"

main() {
    log "Worker starting: $WORKER_ID for task $TASK_ID"

    setup_worker

    # Start Ralph loop for this worker's task
    # Params: prd_file, agent_file, workspace, max_iterations, max_turns_per_session
    if ralph_loop \
        "$WORKER_DIR/prd.md" \
        "$WIGGUM_HOME/config/worker-agent.md" \
        "$WORKER_DIR/workspace" \
        "$MAX_ITERATIONS" \
        "$MAX_TURNS_PER_SESSION"; then
        log "Worker $WORKER_ID completed successfully"
    else
        log_error "Worker $WORKER_ID failed or timed out"
    fi

    cleanup_worker
    log "Worker finished: $WORKER_ID"
}

setup_worker() {
    # Create git worktree for isolation
    cd "$PROJECT_DIR" || exit 1

    log_debug "Creating git worktree at $WORKER_DIR/workspace"
    git worktree add "$WORKER_DIR/workspace" HEAD 2>&1 | tee -a "$WORKER_DIR/worker.log"

    # Setup hooks with workspace boundary enforcement
    export CLAUDE_HOOKS_CONFIG="$WIGGUM_HOME/hooks/worker-hooks.json"
    export WORKER_ID
    export TASK_ID
    export WORKER_WORKSPACE="$WORKER_DIR/workspace"
    export WIGGUM_HOME
}

detect_workspace_violations() {
    local workspace="$1"
    local project_dir="$2"

    log_debug "Checking for workspace boundary violations"

    # Check if any files outside workspace were modified in project root
    cd "$project_dir" || return 0

    # Get list of modified files in project root (excluding .ralph directory)
    local modified_files=$(git status --porcelain 2>/dev/null | grep -v "^.. .ralph/" | awk '{print $2}')

    if [[ -n "$modified_files" ]]; then
        log_error "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        log_error "⚠️  CRITICAL: Workspace boundary violation detected!"
        log_error "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        log_error ""
        log_error "Worker $WORKER_ID modified files outside its workspace:"
        echo "$modified_files" | while read -r file; do
            log_error "  - $file"
        done
        log_error ""
        log_error "Expected workspace: $workspace"
        log_error "Actual modifications: $project_dir"
        log_error ""

        # Create violations log directory if it doesn't exist
        mkdir -p "$project_dir/.ralph/logs"

        # Log violation with timestamp
        {
            echo "================================================================================"
            echo "VIOLATION: Workspace Escape"
            echo "Timestamp: $(date -Iseconds)"
            echo "Worker: $WORKER_ID"
            echo "Task: $TASK_ID"
            echo "Files modified outside workspace:"
            echo "$modified_files"
            echo "================================================================================"
            echo ""
        } >> "$project_dir/.ralph/logs/violations.log"

        log_error "Reverting unauthorized changes..."
        # Revert changes outside workspace
        git checkout -- . 2>&1 | tee -a "$WORKER_DIR/worker.log"

        log_error "Changes have been reverted. Task marked as FAILED."

        return 1
    fi

    log_debug "No workspace violations detected"
    return 0
}

cleanup_worker() {
    log "Cleaning up worker $WORKER_ID"

    local has_violations=false
    local pr_url="N/A"
    local final_status="COMPLETE"

    # Check for workspace violations before processing results
    if ! detect_workspace_violations "$WORKER_DIR/workspace" "$PROJECT_DIR"; then
        log_error "Workspace violation detected - changes outside workspace were reverted"
        echo "WORKSPACE_VIOLATION" > "$WORKER_DIR/violation_status.txt"
        has_violations=true
        final_status="FAILED"
    fi

    # Check PRD status
    local prd_status=$(get_prd_status "$WORKER_DIR/prd.md")
    log "PRD status: $prd_status"

    # Determine final task status
    if [ "$has_violations" = true ]; then
        final_status="FAILED"
        log_error "Task marked as FAILED due to workspace violations"
    elif [ "$prd_status" = "FAILED" ]; then
        final_status="FAILED"
        log_error "Task marked as FAILED - PRD contains failed tasks"
    elif [ "$prd_status" = "INCOMPLETE" ]; then
        final_status="FAILED"
        log_error "Task marked as FAILED - PRD has incomplete tasks (timeout or error)"
    else
        final_status="COMPLETE"
        log "Task completed successfully - all PRD tasks complete"
    fi

    # Only create commits and PRs if no violations and task is complete
    if [ "$has_violations" = false ] && [ "$final_status" = "COMPLETE" ]; then
        if [ -d "$WORKER_DIR/workspace" ]; then
            cd "$WORKER_DIR/workspace" || return 1

            # Get task description from kanban for commit message
            local task_desc=$(grep "**\[$TASK_ID\]**" "$PROJECT_DIR/.ralph/kanban.md" | sed 's/.*\*\*\[.*\]\*\* //' | head -1)

            # Get task priority
            local task_priority=$(grep -A2 "**\[$TASK_ID\]**" "$PROJECT_DIR/.ralph/kanban.md" | grep "Priority:" | sed 's/.*Priority: //')

            # Get task dependencies
            local task_deps=$(grep -A3 "**\[$TASK_ID\]**" "$PROJECT_DIR/.ralph/kanban.md" | grep "Dependencies:" | sed 's/.*Dependencies: //')

            # Commit any changes in the worktree
            if ! git diff --quiet || ! git diff --cached --quiet || [ -n "$(git ls-files --others --exclude-standard)" ]; then
                log "Creating branch and PR for $TASK_ID"

                # Create a branch for this task
                local branch_name="task/$TASK_ID"
                git checkout -b "$branch_name" 2>&1 | tee -a "$WORKER_DIR/worker.log"

                # Stage all changes
                git add -A

                # Create commit
                local commit_msg="${TASK_ID}: ${task_desc}

Worker: $WORKER_ID
Priority: ${task_priority:-MEDIUM}
Completed by Chief Wiggum autonomous worker.

Co-Authored-By: Chief Wiggum Worker <noreply@chief-wiggum.local>"

                git commit -m "$commit_msg" 2>&1 | tee -a "$WORKER_DIR/worker.log"

                local commit_hash=$(git rev-parse HEAD)
                log "Created commit: $commit_hash on branch $branch_name"

                # Push the branch
                if git push -u origin "$branch_name" 2>&1 | tee -a "$WORKER_DIR/worker.log"; then
                    log "Pushed branch $branch_name to remote"

                    # Create Pull Request using gh CLI
                    if command -v gh &> /dev/null; then
                        local pr_body="## Summary
Automated PR for $TASK_ID created by Chief Wiggum worker.

**Task Description:** $task_desc
**Priority:** ${task_priority:-MEDIUM}
**Dependencies:** ${task_deps:-none}
**Worker ID:** $WORKER_ID

## Changes
This PR contains the automated implementation of the task requirements.

---
🤖 Generated by [Chief Wiggum](https://github.com/0kenx/chief-wiggum)"

                        if gh pr create \
                            --title "$TASK_ID: $task_desc" \
                            --body "$pr_body" \
                            --base main \
                            --head "$branch_name" 2>&1 | tee -a "$WORKER_DIR/worker.log"; then

                            log "✓ Created Pull Request for $TASK_ID"

                            # Save PR URL
                            pr_url=$(gh pr view "$branch_name" --json url -q .url)
                            echo "$pr_url" > "$WORKER_DIR/pr_url.txt"
                        else
                            log "Failed to create PR (gh CLI error), but branch is pushed"
                            pr_url="N/A"
                        fi
                    else
                        log "gh CLI not found, skipping PR creation. Branch pushed: $branch_name"
                        pr_url="N/A"
                    fi
                else
                    log "Failed to push branch (no remote configured?)"
                    pr_url="N/A"
                fi
            else
                log "No changes to commit for $TASK_ID"
                pr_url="N/A (no changes)"
            fi
        fi
    else
        log "Skipping commit and PR creation - task status: $final_status"
    fi

    # Clean up git worktree
    cd "$PROJECT_DIR" || exit 1
    log_debug "Removing git worktree"
    git worktree remove "$WORKER_DIR/workspace" --force 2>&1 | tee -a "$WORKER_DIR/worker.log" || true

    # Update kanban based on final status
    if [ "$final_status" = "COMPLETE" ]; then
        log "Marking task $TASK_ID as complete in kanban"
        if ! update_kanban "$PROJECT_DIR/.ralph/kanban.md" "$TASK_ID"; then
            log_error "Failed to update kanban.md after retries"
        fi

        # Append to changelog only on success
        log "Appending to changelog"
        # Get PR URL if it exists
        if [ -f "$WORKER_DIR/pr_url.txt" ]; then
            pr_url=$(cat "$WORKER_DIR/pr_url.txt")
        fi

        if ! append_changelog "$PROJECT_DIR/.ralph/changelog.md" "$TASK_ID" "$WORKER_ID" "$task_desc" "$pr_url"; then
            log_error "Failed to update changelog.md after retries"
        fi

        log "Worker $WORKER_ID completed task $TASK_ID"
    else
        log_error "Marking task $TASK_ID as FAILED in kanban"
        if ! update_kanban_failed "$PROJECT_DIR/.ralph/kanban.md" "$TASK_ID"; then
            log_error "Failed to update kanban.md after retries"
        fi
        log_error "Worker $WORKER_ID failed task $TASK_ID"
    fi
}

main "$@"
