#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT: autofix.quality-gate (shell override)
#
# Extends the markdown quality-gate with post-decision actions:
#   - PASS: commit, push, and ensure a PR exists
#   - FAIL: discard all uncommitted changes
#
# The markdown base handles the LLM evaluation. This shell layer acts on the
# decision by reading the gate_result from the agent's result file.
# =============================================================================

source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_source_core
source "$WIGGUM_HOME/lib/git/git-operations.sh"
[ -z "${_WIGGUM_SRC_PLATFORM_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/platform.sh"

# Save the md-generated agent_run so we can call it from our override
eval "$(declare -f agent_run | sed '1s/agent_run/_md_quality_gate_run/')"

agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local workspace="$worker_dir/workspace"

    # Run the markdown agent (LLM evaluation + discard on FAIL)
    local md_exit=0
    _md_quality_gate_run "$@" || md_exit=$?

    # Read the gate result from the CURRENT run's result file.
    # agent_find_latest_result searches by agent type ("autofix.quality-gate") but
    # result files are named by step ID ("quality-gate"), so it finds nothing.
    local result_file
    result_file=$(agent_get_result_path "$worker_dir")
    local gate_result="FAIL"
    if [[ -n "$result_file" ]] && [[ -f "$result_file" ]]; then
        gate_result=$(jq -r '.outputs.gate_result // "FAIL"' "$result_file" 2>/dev/null)
    fi

    if [[ "$gate_result" != "PASS" ]]; then
        log "Quality gate FAIL — discarding uncommitted changes"
        git -C "$workspace" checkout -- . 2>/dev/null || true
        git -C "$workspace" clean -fd 2>/dev/null || true
        _verify_workspace_clean "$workspace" "FAIL"
        return "$md_exit"
    fi

    # --- PASS path: commit, push, ensure PR ---

    # Check for uncommitted changes to commit
    if git -C "$workspace" diff --quiet 2>/dev/null \
        && git -C "$workspace" diff --cached --quiet 2>/dev/null \
        && [[ -z "$(git -C "$workspace" ls-files --others --exclude-standard 2>/dev/null)" ]]; then
        log_debug "Quality gate PASS but no uncommitted changes to commit"
        return "$md_exit"
    fi

    # Check for leftover artifacts/temp files in git-untracked non-ignored space
    local untracked_artifacts
    untracked_artifacts=$(git -C "$workspace" ls-files --others --exclude-standard \
        | grep -iE '\.(tmp|bak|orig|swp|swo|pyc|pyo|DS_Store|log)$|~$|^\.#|__pycache__|\.cache/|node_modules/|package-lock\.json|pnpm-lock\.yaml|yarn\.lock|Gemfile\.lock|poetry\.lock|composer\.lock|Cargo\.lock|go\.sum' \
        2>/dev/null || true)
    if [[ -n "$untracked_artifacts" ]]; then
        log_warn "Leftover artifacts detected — cleaning before commit:"
        log_warn "$untracked_artifacts"
        local artifact
        while IFS= read -r artifact; do
            [[ -n "$artifact" ]] && rm -f "$workspace/$artifact"
        done <<< "$untracked_artifacts"
    fi

    # Stage and commit
    git_set_identity
    git -C "$workspace" add -A 2>/dev/null

    # Build commit message including auditor's original scope (shell-only,
    # not exposed to the quality-gate LLM prompt — preserves blind review)
    local task_id="${WIGGUM_TASK_ID:-autofix}"
    local commit_msg
    commit_msg=$(_build_commit_msg "$worker_dir" "$task_id")
    local commit_exit=0
    git -C "$workspace" commit --no-gpg-sign -m "$commit_msg" 2>&1 || commit_exit=$?
    if [[ "$commit_exit" -ne 0 ]]; then
        log_warn "Commit failed (exit=$commit_exit), skipping push/PR"
        return "$md_exit"
    fi

    local commit_sha
    commit_sha=$(git -C "$workspace" rev-parse HEAD 2>/dev/null)
    log "Committed: ${commit_sha:0:8}"

    # Verify no leftover artifacts after commit
    _verify_workspace_clean "$workspace" "PASS"

    # Push
    local current_branch
    current_branch=$(git -C "$workspace" rev-parse --abbrev-ref HEAD 2>/dev/null)

    local push_exit=0
    git -C "$workspace" push -u origin "$current_branch" 2>&1 || push_exit=$?
    if [[ "$push_exit" -ne 0 ]]; then
        # Retry with force-with-lease (safe for single-owner task branches)
        push_exit=0
        git -C "$workspace" push --force-with-lease -u origin "$current_branch" 2>&1 || push_exit=$?
    fi
    if [[ "$push_exit" -ne 0 ]]; then
        log_warn "Push failed (exit=$push_exit)"
        return "$md_exit"
    fi
    log "Pushed to $current_branch"

    # Ensure PR exists
    _ensure_pr "$workspace" "$current_branch" "$worker_dir" "$project_dir"

    return "$md_exit"
}

# Build a commit message that includes the auditor's original scope/concern.
# Falls back to a generic message if the audit report is unavailable.
#
# Args:
#   worker_dir - Worker directory
#   task_id    - Task identifier
#
# Returns: commit message string (via stdout)
_build_commit_msg() {
    local worker_dir="$1"
    local task_id="$2"

    # Find the latest random-audit report
    local audit_report
    audit_report=$(agent_find_latest_report "$worker_dir" "random-audit")

    if [[ -z "$audit_report" ]] || [[ ! -f "$audit_report" ]]; then
        echo "$task_id: automated code improvement"
        return
    fi

    # Extract scope and concern from the structured report
    local scope_target concern
    scope_target=$(grep -m1 '^\- \*\*Scope target\*\*:' "$audit_report" 2>/dev/null \
        | sed 's/^- \*\*Scope target\*\*: *//' | sed 's/[[:space:]]*$//' || true)
    concern=$(grep -m1 '^\- \*\*Concern\*\*:' "$audit_report" 2>/dev/null \
        | sed 's/^- \*\*Concern\*\*: *//' | sed 's/[[:space:]]*$//' || true)

    if [[ -n "$concern" ]]; then
        local scope_part=""
        if [[ -n "$scope_target" ]] && [[ "$scope_target" != "entire codebase" ]]; then
            scope_part=" in ${scope_target}"
        fi
        # Lowercase the concern for commit message style
        local concern_lower
        concern_lower=$(echo "$concern" | tr '[:upper:]' '[:lower:]' | sed 's/^[[:space:]]*//')
        echo "$task_id: autofix ${concern_lower}${scope_part}"
    else
        echo "$task_id: automated code improvement"
    fi
}

# Verify no untracked non-ignored files remain in workspace after cleanup.
# Logs a warning if artifacts are found — helps catch missed cleanup.
#
# Args:
#   workspace - Git workspace directory
#   context   - Context label for logging (e.g., "FAIL", "PASS")
_verify_workspace_clean() {
    local workspace="$1"
    local context="$2"

    local remaining
    remaining=$(git -C "$workspace" ls-files --others --exclude-standard 2>/dev/null || true)
    if [[ -n "$remaining" ]]; then
        log_warn "Workspace not clean after $context — leftover files:"
        log_warn "$remaining"
    fi
}

# Create a PR for the branch if one doesn't already exist.
#
# Args:
#   workspace   - Git workspace directory
#   branch      - Branch name
#   worker_dir  - Worker directory
#   project_dir - Project directory
_ensure_pr() {
    local workspace="$1"
    local branch="$2"
    local worker_dir="$3"
    local project_dir="${4:-${PROJECT_DIR:-}}"

    if ! command -v gh &>/dev/null; then
        log_debug "gh CLI not found, skipping PR creation"
        return 0
    fi

    local gh_timeout="${WIGGUM_GH_TIMEOUT:-30}"

    # Check if a PR already exists for this branch
    local existing_url
    existing_url=$(timeout "$gh_timeout" gh pr view "$branch" --json url -q '.url' 2>/dev/null || true)
    if [[ -n "$existing_url" ]]; then
        log "PR exists: $existing_url"
        echo "$existing_url" > "$worker_dir/pr_url.txt"
        return 0
    fi

    local default_branch
    default_branch=$(git -C "$workspace" rev-parse --abbrev-ref origin/HEAD 2>/dev/null \
        | sed 's|origin/||') || default_branch="main"
    [[ -z "$default_branch" ]] && default_branch="main"

    local task_id="${WIGGUM_TASK_ID:-autofix}"
    local title="$task_id: automated code improvements"
    local body
    body="Automated code improvements from the autofix pipeline.

Each commit was independently audited, verified, and quality-gated before inclusion.

---
Generated by Chief Wiggum"

    local pr_output
    pr_output=$(timeout "$gh_timeout" gh pr create \
        --title "$title" \
        --body "$body" \
        --base "$default_branch" \
        --head "$branch" 2>&1) || {
        log_warn "Failed to create PR: ${pr_output:0:200}"
        return 0
    }

    local pr_url
    pr_url=$(timeout "$gh_timeout" gh pr view "$branch" --json url -q '.url' 2>/dev/null || true)
    if [[ -n "$pr_url" ]]; then
        log "Created PR: $pr_url"
        echo "$pr_url" > "$worker_dir/pr_url.txt"
    fi
}
