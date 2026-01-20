#!/usr/bin/env bash
# Worker script - spawned by wiggum for each task
# Acts as a thin coordinator that invokes agents via the agent-registry.

WORKER_DIR="$1"         # e.g., .ralph/workers/worker-TASK-001-12345
PROJECT_DIR="$2"        # Project root directory
WIGGUM_HOME="${WIGGUM_HOME:-$HOME/.claude/chief-wiggum}"

# Extract WORKER_ID and TASK_ID from WORKER_DIR
# WORKER_DIR format: .ralph/workers/worker-TASK-001-12345
WORKER_ID=$(basename "$WORKER_DIR")  # e.g., worker-TASK-001-12345
TASK_ID=$(echo "$WORKER_ID" | sed -E 's/worker-(TASK-[0-9]+)-.*/\1/')  # e.g., TASK-001

# Source shared libraries
source "$WIGGUM_HOME/lib/agent-registry.sh"
source "$WIGGUM_HOME/lib/logger.sh"
source "$WIGGUM_HOME/lib/file-lock.sh"
source "$WIGGUM_HOME/lib/audit-logger.sh"
source "$WIGGUM_HOME/lib/task-parser.sh"
source "$WIGGUM_HOME/lib/git-operations.sh"
source "$WIGGUM_HOME/lib/metrics-export.sh"

# Save references to sourced kanban functions before defining wrapper
eval "_kanban_mark_done() $(declare -f update_kanban | sed '1d')"
eval "_kanban_mark_failed() $(declare -f update_kanban_failed | sed '1d')"

# Set log file for this worker - all log() calls will also write here
export LOG_FILE="$WORKER_DIR/worker.log"

main() {
    log "Worker starting: $WORKER_ID for task $TASK_ID"

    # Track if shutdown was requested
    local worker_interrupted=false
    local agent_pid=""

    # Setup signal handlers for graceful shutdown
    handle_worker_shutdown() {
        log "Worker $WORKER_ID received shutdown signal"
        worker_interrupted=true

        # Kill agent if it's running
        if [ -n "$agent_pid" ] && kill -0 "$agent_pid" 2>/dev/null; then
            log "Terminating agent (PID: $agent_pid)"
            kill -TERM "$agent_pid" 2>/dev/null || true
            wait "$agent_pid" 2>/dev/null || true
        fi

        # Exit immediately to stop the worker
        exit 143  # Standard exit code for SIGTERM (128 + 15)
    }
    trap handle_worker_shutdown INT TERM

    # Log worker start to audit log
    audit_log_worker_start "$TASK_ID" "$WORKER_ID"

    setup_worker

    # Handle resume mode - pass environment variables to agent
    if [ -n "${WIGGUM_RESUME_ITERATION:-}" ]; then
        log "Worker resuming from iteration $WIGGUM_RESUME_ITERATION"
        export WIGGUM_RESUME_ITERATION
        export WIGGUM_RESUME_CONTEXT
    fi

    # Run task-worker agent in background to capture PID
    run_agent "task-worker" "$WORKER_DIR" "$PROJECT_DIR" &
    local agent_pid=$!

    # Wait for agent to complete
    if wait "$agent_pid"; then
        if [ "$worker_interrupted" = true ]; then
            log "Worker $WORKER_ID interrupted by signal"
        else
            log "Worker $WORKER_ID task-worker agent completed successfully"
        fi
    else
        if [ "$worker_interrupted" = true ]; then
            log "Worker $WORKER_ID interrupted by signal"
        else
            log_error "Worker $WORKER_ID task-worker agent failed or timed out"
        fi
    fi

    # Run validation-review agent on completed work
    if [ -d "$WORKER_DIR/workspace" ]; then
        log "Running validation review on completed work"
        run_agent "validation-review" "$WORKER_DIR" "$PROJECT_DIR" 5
    fi

    # Determine final status
    determine_finality
    local has_violations="$FINALITY_HAS_VIOLATIONS"
    local final_status="$FINALITY_STATUS"

    # Check validation result - override final_status if validation failed
    if [ -f "$WORKER_DIR/validation-result.txt" ]; then
        local validation_result=$(cat "$WORKER_DIR/validation-result.txt")
        if [ "$validation_result" = "FAIL" ]; then
            log_error "Validation review FAILED - marking task as failed"
            final_status="FAILED"
        elif [ "$validation_result" = "UNKNOWN" ]; then
            log_error "Validation result UNKNOWN - cannot proceed safely"
            log_error "Worker exiting without commit/PR or status update"
            return 1
        fi
    fi
    local pr_url="N/A"
    local task_desc=""

    # Only create commits and PRs if no violations and task is complete
    if [ "$has_violations" = false ] && [ "$final_status" = "COMPLETE" ]; then
        if [ -d "$WORKER_DIR/workspace" ]; then
            cd "$WORKER_DIR/workspace" || return 1

            # Get task description from kanban for commit message
            task_desc=$(grep "**\[$TASK_ID\]**" "$PROJECT_DIR/.ralph/kanban.md" | sed 's/.*\*\*\[.*\]\*\* //' | head -1)

            # Get task priority
            local task_priority=$(grep -A2 "**\[$TASK_ID\]**" "$PROJECT_DIR/.ralph/kanban.md" | grep "Priority:" | sed 's/.*Priority: //')

            # Create commit using shared library
            if git_create_commit "$WORKER_DIR/workspace" "$TASK_ID" "$task_desc" "$task_priority" "$WORKER_ID"; then
                local branch_name="$GIT_COMMIT_BRANCH"

                # Create PR using shared library
                git_create_pr "$branch_name" "$TASK_ID" "$task_desc" "$WORKER_DIR" "$PROJECT_DIR"
                pr_url="$GIT_PR_URL"
            else
                final_status="FAILED"
            fi
        fi
    else
        log "Skipping commit and PR creation - task status: $final_status"
    fi

    cleanup_worker "$final_status" "$task_desc" "$pr_url"
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

    # Store worker PID for tracking by orchestrator
    echo "$$" > "$WORKER_DIR/worker.pid"
    log_debug "Stored worker PID $$ in $WORKER_DIR/worker.pid"
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

        log_error "NOT reverting changes - may include user edits from main repo."
        log_error "Task marked as FAILED. Please manually review the changes."
        log_error ""
        log_error "To prevent this:"
        log_error "  1. Do NOT edit files in the main repo while workers are running"
        log_error "  2. Ensure your git working directory is clean before running 'wiggum run'"
        log_error ""

        return 1
    fi

    log_debug "No workspace violations detected"
    return 0
}

determine_finality() {
    local has_violations=false
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

    # Return values via global variables (bash limitation)
    FINALITY_HAS_VIOLATIONS="$has_violations"
    FINALITY_STATUS="$final_status"
}

cleanup_worktree() {
    local final_status="$1"

    # Clean up git worktree (only on full success - verify actual GitHub state)
    cd "$PROJECT_DIR" || exit 1
    local can_cleanup=false
    if [ "$final_status" = "COMPLETE" ]; then
        # Use shared library to verify push status
        if git_verify_pushed "$WORKER_DIR/workspace" "$TASK_ID"; then
            can_cleanup=true
        fi
    fi

    if [ "$can_cleanup" = true ]; then
        log_debug "Removing git worktree"
        git worktree remove "$WORKER_DIR/workspace" --force 2>&1 | tee -a "$WORKER_DIR/worker.log" || true
    else
        log "Preserving worktree for debugging: $WORKER_DIR/workspace"
    fi
}

update_kanban() {
    local final_status="$1"
    local task_desc="$2"
    local pr_url="$3"

    # Update kanban based on final status
    if [ "$final_status" = "COMPLETE" ]; then
        log "Marking task $TASK_ID as complete in kanban"
        if ! _kanban_mark_done "$PROJECT_DIR/.ralph/kanban.md" "$TASK_ID"; then
            log_error "Failed to update kanban.md after retries"
        fi

        # Append to changelog only on success
        log "Appending to changelog"
        # Get PR URL if it exists
        if [ -f "$WORKER_DIR/pr_url.txt" ]; then
            pr_url=$(cat "$WORKER_DIR/pr_url.txt")
        fi

        # Get detailed summary if it exists
        local summary=""
        if [ -f "$WORKER_DIR/summary.txt" ]; then
            summary=$(cat "$WORKER_DIR/summary.txt")
            log "Including detailed summary in changelog"
        fi

        if ! append_changelog "$PROJECT_DIR/.ralph/changelog.md" "$TASK_ID" "$WORKER_ID" "$task_desc" "$pr_url" "$summary"; then
            log_error "Failed to update changelog.md after retries"
        fi

        log "Worker $WORKER_ID completed task $TASK_ID"
    else
        log_error "Marking task $TASK_ID as FAILED in kanban"
        if ! _kanban_mark_failed "$PROJECT_DIR/.ralph/kanban.md" "$TASK_ID"; then
            log_error "Failed to update kanban.md after retries"
        fi
        log_error "Worker $WORKER_ID failed task $TASK_ID"
    fi

    # Log final worker status to audit log
    audit_log_worker_complete "$TASK_ID" "$WORKER_ID" "$final_status"

    # Update metrics.json with latest worker data
    log_debug "Exporting metrics to metrics.json"
    export_metrics "$PROJECT_DIR/.ralph" 2>/dev/null || true

    # Remove worker PID file
    rm -f "$WORKER_DIR/worker.pid"
    log_debug "Removed worker PID file"
}

cleanup_worker() {
    local final_status="$1"
    local task_desc="$2"
    local pr_url="$3"

    log "Cleaning up worker $WORKER_ID"

    # Log cleanup start to audit log
    audit_log_worker_cleanup "$TASK_ID" "$WORKER_ID"

    # Clean up git worktree
    cleanup_worktree "$final_status"

    # Update kanban and finalize
    update_kanban "$final_status" "$task_desc" "$pr_url"
}

main "$@"
