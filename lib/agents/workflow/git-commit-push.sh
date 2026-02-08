#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: git-commit-push
# AGENT_DESCRIPTION: Git commit and push agent that stages all changes, creates
#   a commit, and pushes to the remote branch. Pure bash, no LLM involved.
# REQUIRED_PATHS:
#   - workspace : Directory containing the git repository
# OUTPUT_FILES:
#   - commit-push-result.json : Contains PASS or FAIL with commit SHA
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "workflow.git-commit-push" "Git stage, commit and push changes"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Source dependencies
agent_source_core
source "$WIGGUM_HOME/lib/git/git-operations.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local commit_message="${3:-${WIGGUM_TASK_ID:+${WIGGUM_TASK_ID}: }${WIGGUM_STEP_ID:-commit} - commit-push}"

    local workspace="$worker_dir/workspace"

    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Workspace not found"]'
        return 1
    fi

    # Verify workspace is a git repository
    if [ ! -d "$workspace/.git" ] && ! git -C "$workspace" rev-parse --git-dir &>/dev/null; then
        log_error "Workspace is not a git repository: $workspace"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Not a git repository"]'
        return 1
    fi

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Set up context
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"

    # Check if there are uncommitted changes to commit
    local has_uncommitted_changes=false
    if ! git -C "$workspace" diff --quiet 2>/dev/null; then
        has_uncommitted_changes=true
    elif ! git -C "$workspace" diff --cached --quiet 2>/dev/null; then
        has_uncommitted_changes=true
    elif [ -n "$(git -C "$workspace" ls-files --others --exclude-standard 2>/dev/null)" ]; then
        has_uncommitted_changes=true
    fi

    # Check if there are unpushed commits (e.g., from readonly agent checkpoints)
    local has_unpushed_commits=false
    local unpushed_count=0
    if git -C "$workspace" rev-parse --verify '@{u}' &>/dev/null; then
        unpushed_count=$(git -C "$workspace" rev-list '@{u}..HEAD' --count 2>/dev/null || echo "0")
        if [ "$unpushed_count" -gt 0 ]; then
            has_unpushed_commits=true
            log "Found $unpushed_count unpushed commit(s)"
        fi
    fi

    if [ "$has_uncommitted_changes" = false ] && [ "$has_unpushed_commits" = false ]; then
        log "No changes to commit or push"
        agent_write_result "$worker_dir" "PASS" '{"commit_sha":"","push_status":"no_changes"}'
        return 0
    fi

    # Get current branch
    local current_branch
    current_branch=$(git -C "$workspace" rev-parse --abbrev-ref HEAD 2>/dev/null)

    # Handle detached HEAD - create a task branch
    if [ "$current_branch" = "HEAD" ]; then
        # Extract task_id from worker directory name
        local worker_id task_id
        worker_id=$(basename "$worker_dir")
        task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/')

        if [ -n "$task_id" ] && [ "$task_id" != "$worker_id" ]; then
            current_branch="task/${task_id}-$(epoch_now)"
            log "Detached HEAD - creating branch: $current_branch"
            if ! git -C "$workspace" checkout -b "$current_branch" 2>&1; then
                log_error "Failed to create branch from detached HEAD"
                agent_write_result "$worker_dir" "FAIL" '{}' '["Failed to create branch from detached HEAD"]'
                return 1
            fi
        else
            log_error "Not on a branch (detached HEAD state) and cannot extract task ID"
            agent_write_result "$worker_dir" "FAIL" '{}' '["Detached HEAD - not on a branch"]'
            return 1
        fi
    fi

    # Get commit SHA (may be updated if we create a new commit)
    local commit_sha
    commit_sha=$(git -C "$workspace" rev-parse HEAD 2>/dev/null)

    # Only create a new commit if there are uncommitted changes
    if [ "$has_uncommitted_changes" = true ]; then
        log "Committing changes on branch: $current_branch"

        # Stage all changes
        if ! git -C "$workspace" add -A 2>&1; then
            log_error "Failed to stage changes"
            agent_write_result "$worker_dir" "FAIL" '{}' '["Failed to stage changes"]'
            return 1
        fi

        # Set git author/committer identity
        git_set_identity

        # Check for resolution plan to customize commit message
        if [ -f "$worker_dir/resolution-plan.md" ]; then
            commit_message="${WIGGUM_TASK_ID:+${WIGGUM_TASK_ID}: }${WIGGUM_STEP_ID:-resolve} - conflict-resolution"
        fi

        # Create commit
        local commit_output
        if ! commit_output=$(git -C "$workspace" commit --no-gpg-sign -m "$commit_message" 2>&1); then
            log_error "Failed to create commit: $commit_output"
            agent_write_result "$worker_dir" "FAIL" '{}' '["Commit failed: '"${commit_output:0:200}"'"]'
            return 1
        fi

        commit_sha=$(git -C "$workspace" rev-parse HEAD 2>/dev/null)
        log "Created commit: $commit_sha"
    else
        log "No uncommitted changes, pushing $unpushed_count existing commit(s) on branch: $current_branch"
    fi

    # Push to remote
    log "Pushing to remote..."
    local push_output push_exit=0
    push_output=$(git -C "$workspace" push 2>&1) || push_exit=$?

    # If push rejected (non-fast-forward), retry with --force-with-lease.
    # This is safe because task branches are single-owner — no one else pushes
    # to them. Common after rebase (sync-main rewrites branch history).
    if [ $push_exit -ne 0 ] && echo "$push_output" | grep -qE "(rejected|non-fast-forward)"; then
        # Dry-run validates the lease (stale info check) without side effects.
        # Server-side hooks (GH013) are NOT triggered by dry-run, so the actual
        # push is still needed to detect repo-rule rejections.
        log "Push rejected (non-fast-forward) — probing with --force-with-lease --dry-run"
        push_exit=0
        push_output=$(git -C "$workspace" push --force-with-lease --dry-run 2>&1) || push_exit=$?

        if [ $push_exit -ne 0 ]; then
            # Dry-run failed (stale refs, no upstream, etc.) — skip straight to
            # rebase fallback since force-push can't succeed either
            log "Force-with-lease dry-run failed — falling back to rebase + push"
        else
            # Lease is valid — attempt the actual force-with-lease push
            log "Lease valid — pushing with --force-with-lease"
            push_output=$(git -C "$workspace" push --force-with-lease 2>&1) || push_exit=$?
        fi

        # If force-push blocked by repo rules (e.g., GitHub GH013), or dry-run
        # failed, fall back to rebase onto remote tracking branch + regular push.
        # Safe because task branches are single-owner.
        if [ $push_exit -ne 0 ]; then
            log "Force-push failed — falling back to rebase + push"
            push_exit=0
            if git -C "$workspace" fetch origin "$current_branch" 2>/dev/null \
               && git -C "$workspace" rebase "origin/$current_branch" 2>/dev/null; then
                commit_sha=$(git -C "$workspace" rev-parse HEAD 2>/dev/null)
                push_output=$(git -C "$workspace" push 2>&1) || push_exit=$?
            else
                # Rebase failed — abort and report
                git -C "$workspace" rebase --abort 2>/dev/null || true
                push_exit=1
                push_output="Rebase onto origin/$current_branch failed"
            fi
        fi
    fi

    if [ $push_exit -ne 0 ]; then
        log_error "Failed to push: $push_output"
        agent_write_result "$worker_dir" "FAIL" \
            "{\"commit_sha\":\"$commit_sha\"}" \
            '["Push failed: '"${push_output:0:200}"'"]'
        return 1
    fi

    log "Successfully pushed to $current_branch"
    agent_write_result "$worker_dir" "PASS" \
        "{\"commit_sha\":\"$commit_sha\",\"push_status\":\"success\",\"branch\":\"$current_branch\"}"
    return 0
}
