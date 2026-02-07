#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: git-sync-main
# AGENT_DESCRIPTION: Git sync agent that fetches and merges origin/main into
#   the current branch. Pure bash, no LLM involved. Detects merge conflicts.
# REQUIRED_PATHS:
#   - workspace : Directory containing the git repository
# OUTPUT_FILES:
#   - sync-result.json : Contains PASS (clean merge) or FAIL (conflicts)
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "workflow.git-sync-main" "Git fetch and merge from origin/main"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Source dependencies
agent_source_core
source "$WIGGUM_HOME/lib/git/git-operations.sh"

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"

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

    log "Fetching origin/main..."

    # Fetch origin/main
    local fetch_output
    if ! fetch_output=$(git -C "$workspace" fetch origin main 2>&1); then
        log_error "Failed to fetch origin/main: $fetch_output"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Fetch failed: '"${fetch_output:0:200}"'"]'
        return 1
    fi

    # Pre-flight: abort stale MERGE_HEAD / REBASE_HEAD from previous incomplete operations.
    # Without this, git merge/rebase fails immediately.
    if git -C "$workspace" rev-parse --verify MERGE_HEAD &>/dev/null; then
        log_warn "Stale MERGE_HEAD detected - aborting incomplete merge before retry"
        git -C "$workspace" merge --abort 2>/dev/null || true
    fi
    if [ -d "$workspace/.git/rebase-merge" ] || [ -d "$workspace/.git/rebase-apply" ]; then
        log_warn "Stale rebase state detected - aborting incomplete rebase before retry"
        git -C "$workspace" rebase --abort 2>/dev/null || true
    fi

    # Set git identity for merge/rebase commits
    git_set_identity

    # =========================================================================
    # Sync strategy: ff-only → rebase → merge (cheapest to most expensive)
    #
    # F: Fast-forward for trivial syncs — no merge commit when branch is behind
    # A: Rebase for linear history — preferred over merge commits because task
    #    branches are single-owner (no shared history to break)
    # Fallback: Merge creates a single conflict resolution point, which is
    #    better for LLM resolution than rebase's per-commit conflicts
    # =========================================================================

    # Step 1: Try fast-forward (no merge commit, cheapest)
    log "Syncing with origin/main..."
    local ff_output ff_exit=0
    ff_output=$(git -C "$workspace" merge --ff-only origin/main 2>&1) || ff_exit=$?

    if [ $ff_exit -eq 0 ]; then
        if echo "$ff_output" | grep -q "Already up to date"; then
            log "Already up to date with origin/main"
            agent_write_result "$worker_dir" "PASS" '{"merge_status":"up_to_date","strategy":"ff","conflicts":0}'
        else
            log "Fast-forwarded to origin/main (no merge commit needed)"
            agent_write_result "$worker_dir" "PASS" '{"merge_status":"fast_forward","strategy":"ff","conflicts":0}'
        fi
        return 0
    fi

    # Step 2: Try rebase (linear history, safe on single-owner branches)
    log "Fast-forward not possible — attempting rebase onto origin/main..."
    local rebase_exit=0
    git -C "$workspace" rebase origin/main >/dev/null 2>&1 || rebase_exit=$?

    if [ $rebase_exit -eq 0 ]; then
        log "Rebased onto origin/main (linear history preserved)"
        agent_write_result "$worker_dir" "PASS" '{"merge_status":"rebased","strategy":"rebase","conflicts":0}'
        return 0
    fi

    # Rebase failed (conflicts on one or more commits) — abort and fall back to merge.
    # Merge creates a single conflict resolution point which is better for LLM
    # resolution than rebase's per-commit conflict resolution.
    git -C "$workspace" rebase --abort 2>/dev/null || true
    log "Rebase had conflicts — falling back to merge (single resolution point)"

    # Step 3: Fall back to merge
    local merge_output merge_exit=0
    merge_output=$(git -C "$workspace" merge origin/main --no-edit 2>&1) || merge_exit=$?

    if [ $merge_exit -eq 0 ]; then
        log "Successfully merged origin/main"
        agent_write_result "$worker_dir" "PASS" '{"merge_status":"merged","strategy":"merge","conflicts":0}'
        return 0
    fi

    # Check if merge failed due to conflicts
    local conflicted_files
    conflicted_files=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null || true)

    if [ -n "$conflicted_files" ]; then
        local conflict_count
        conflict_count=$(echo "$conflicted_files" | wc -l)
        log "Merge conflict detected: $conflict_count file(s)"

        # Build list of conflicted files for output
        local files_json
        files_json=$(echo "$conflicted_files" | jq -R -s 'split("\n") | map(select(length > 0))')

        agent_write_result "$worker_dir" "FAIL" \
            "{\"merge_status\":\"conflict\",\"strategy\":\"merge\",\"conflicts\":$conflict_count,\"conflicted_files\":$files_json}"
        return 0  # Return 0 because FAIL is a valid gate result, not an error
    fi

    # Some other merge failure
    log_error "Merge failed: $merge_output"
    agent_write_result "$worker_dir" "FAIL" '{}' '["Merge failed: '"${merge_output:0:200}"'"]'
    return 1
}
