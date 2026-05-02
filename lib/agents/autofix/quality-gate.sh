#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT: autofix.quality-gate (shell override)
#
# Extends the markdown quality-gate with post-decision actions:
#   - PASS: commit, push (with backoff), create PR
#   - FAIL: discard changes (reset workspace to clean state)
#
# Workspace cleanup is NOT done here — it is handled by `wiggum service stop`
# when the service is shut down. This allows the pipeline to loop back to
# random-audit with the workspace intact for the next audit cycle.
#
# The markdown base handles the LLM evaluation. This shell layer acts on the
# decision by reading the gate_result from the agent's result file.
# =============================================================================

source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_source_core
source "$WIGGUM_HOME/lib/git/git-operations.sh"
source "$WIGGUM_HOME/lib/git/worktree-helpers.sh"
[ -z "${_WIGGUM_SRC_PLATFORM_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/platform.sh"

# Save the md-generated agent_run so we can call it from our override
eval "$(declare -f agent_run | sed '1s/agent_run/_md_quality_gate_run/')"

AUTOFIX_CURRENT_AUDIT_FINGERPRINT=""
AUTOFIX_LAST_PR_URL=""
AUTOFIX_PASS_ACTION=""

agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local workspace="$worker_dir/workspace"

    # Run the markdown agent (LLM evaluation)
    local md_exit=0
    _md_quality_gate_run "$@" || md_exit=$?

    # Read the gate result from the CURRENT run's result file.
    local result_file
    result_file=$(agent_get_result_path "$worker_dir")
    local gate_result="FAIL"
    if [[ -n "$result_file" ]] && [[ -f "$result_file" ]]; then
        gate_result=$(jq -r '.outputs.gate_result // "FAIL"' "$result_file" 2>/dev/null)
    fi

    if [[ "$gate_result" == "PASS" ]]; then
        if _handle_pass "$workspace" "$worker_dir" "$project_dir"; then
            case "${AUTOFIX_PASS_ACTION:-}" in
                duplicate_skipped)
                    log "Quality gate PASS — duplicate audit skipped"
                    ;;
                no_changes)
                    log "Quality gate PASS — no changes to publish"
                    ;;
                branch_pushed)
                    log "Quality gate PASS — branch pushed, PR creation failed"
                    ;;
                *)
                    log "Quality gate PASS — push/PR succeeded"
                    ;;
            esac
            # Reset workspace to main so the next audit cycle starts clean
            _reset_workspace_to_main "$workspace" "$project_dir"
        else
            log_warn "Quality gate PASS — push/PR failed, leaving workspace for inspection"
        fi
    else
        log "Quality gate FAIL — discarding changes"
        _reset_workspace_to_main "$workspace" "$project_dir"
    fi

    return "$md_exit"
}

# Handle PASS: commit changes, push per-cycle branch with backoff, create PR.
#
# Returns: 0 if push+PR succeeded, 1 if any step failed
_handle_pass() {
    local workspace="$1"
    local worker_dir="$2"
    local project_dir="$3"
    AUTOFIX_CURRENT_AUDIT_FINGERPRINT=""
    AUTOFIX_LAST_PR_URL=""
    AUTOFIX_PASS_ACTION=""

    # Check for uncommitted changes to commit
    if git -C "$workspace" diff --quiet 2>/dev/null \
        && git -C "$workspace" diff --cached --quiet 2>/dev/null \
        && [[ -z "$(git -C "$workspace" ls-files --others --exclude-standard 2>/dev/null)" ]]; then
        log_debug "Quality gate PASS but no uncommitted changes to commit"
        AUTOFIX_PASS_ACTION="no_changes"
        return 0
    fi

    # Resolve the audit report ONCE to prevent race conditions.
    # Prefer the report that verify-fix actually consumed; falling back to the
    # latest random-audit report is only for older result files.
    local audit_report
    audit_report=$(_resolve_cycle_audit_report "$worker_dir")

    local task_id="${WIGGUM_TASK_ID:-autofix}"
    local commit_msg
    commit_msg=$(_build_commit_msg "$task_id" "$audit_report")

    if [[ -n "$audit_report" ]] && [[ -f "$audit_report" ]]; then
        local reserve_rc=0
        _autofix_reserve_audit "$audit_report" "$worker_dir" "$project_dir" "$commit_msg" || reserve_rc=$?
        if [[ "$reserve_rc" -eq 2 ]]; then
            log "Autofix duplicate audit detected — skipping PR for this cycle"
            AUTOFIX_PASS_ACTION="duplicate_skipped"
            return 0
        elif [[ "$reserve_rc" -ne 0 ]]; then
            log_warn "Autofix audit reservation failed (exit=$reserve_rc)"
            return 1
        fi
    else
        log_warn "No random-audit report found — skipping autofix dedupe for this cycle"
    fi

    # Clean leftover artifacts before committing
    _clean_artifacts "$workspace"

    # Stage and commit
    git_set_identity
    git -C "$workspace" add -A 2>/dev/null

    local commit_exit=0
    git -C "$workspace" commit --no-gpg-sign -m "$commit_msg" 2>&1 || commit_exit=$?
    if [[ "$commit_exit" -ne 0 ]]; then
        log_warn "Commit failed (exit=$commit_exit)"
        _autofix_mark_audit_state "$audit_report" "$project_dir" "commit_failed" "" "" \
            || log_warn "Failed to update autofix dedupe state"
        return 1
    fi

    local commit_sha
    commit_sha=$(git -C "$workspace" rev-parse HEAD 2>/dev/null)
    log "Committed: ${commit_sha:0:8}"

    # Push and create PR (with exponential backoff)
    _push_per_cycle_pr "$workspace" "$commit_sha" "$commit_msg" "$worker_dir" "$project_dir" "$audit_report"
}

# Remove leftover artifact files from the workspace before committing.
_clean_artifacts() {
    local workspace="$1"

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
}

# Reset the workspace worktree to a clean state matching the default branch.
# Discards all uncommitted changes and untracked files so the next
# audit cycle starts fresh without needing a new worktree.
#
# Uses detached HEAD instead of checking out the default branch directly,
# because git worktrees cannot checkout a branch that is already checked
# out in another worktree (including the main repo).
#
# Args:
#   workspace   - Git workspace directory (worker_dir/workspace)
#   project_dir - Project directory (git root)
_reset_workspace_to_main() {
    local workspace="$1"
    local project_dir="$2"

    if [[ ! -d "$workspace" ]]; then
        return 0
    fi

    local default_branch
    default_branch=$(get_default_branch)

    # Fetch latest main and detach HEAD at that commit.
    # Using --detach avoids "branch already checked out" errors in worktrees
    # where 'main' is already checked out by the main repo or another worktree.
    git -C "$workspace" fetch origin "$default_branch" 2>/dev/null || true
    git -C "$workspace" checkout --detach "origin/$default_branch" 2>/dev/null || true
    git -C "$workspace" reset --hard "origin/$default_branch" 2>/dev/null || true
    git -C "$workspace" clean -fdx 2>/dev/null || true

    log_debug "Reset workspace to origin/$default_branch (detached)"
}

# Resolve a worker-relative file path to an absolute path.
_worker_file_path() {
    local worker_dir="$1"
    local file_path="${2:-}"

    [[ -z "$file_path" ]] && return 1
    if [[ "$file_path" = /* ]]; then
        echo "$file_path"
    else
        echo "$worker_dir/$file_path"
    fi
}

# Resolve the audit report associated with the current autofix cycle.
#
# verify-fix records the parent_report_file it used. That is the authoritative
# audit report for PR title/body generation; latest random-audit is only a
# compatibility fallback for older result files.
_resolve_cycle_audit_report() {
    local worker_dir="$1"

    local verify_result parent_report parent_path
    verify_result=$(agent_find_latest_result "$worker_dir" "verify-fix")
    if [[ -n "$verify_result" ]] && [[ -f "$verify_result" ]]; then
        parent_report=$(jq -r '.outputs.parent_report_file // ""' "$verify_result" 2>/dev/null)
        if [[ -n "$parent_report" ]]; then
            parent_path=$(_worker_file_path "$worker_dir" "$parent_report")
            if [[ -f "$parent_path" ]]; then
                echo "$parent_path"
                return 0
            fi
        fi
    fi

    local audit_result audit_report audit_path
    audit_result=$(agent_find_latest_result "$worker_dir" "random-audit")
    if [[ -n "$audit_result" ]] && [[ -f "$audit_result" ]]; then
        audit_report=$(jq -r '.outputs.report_file // ""' "$audit_result" 2>/dev/null)
        if [[ -n "$audit_report" ]]; then
            audit_path=$(_worker_file_path "$worker_dir" "$audit_report")
            if [[ -f "$audit_path" ]]; then
                echo "$audit_path"
                return 0
            fi
        fi
    fi

    agent_find_latest_report "$worker_dir" "random-audit"
}

# Build a commit message that includes the auditor's original scope/concern.
# Falls back to a generic message if the audit report is unavailable.
#
# Args:
#   task_id      - Task identifier
#   audit_report - Path to the audit report file (resolved by caller)
#
# Returns: commit message string (via stdout)
_build_commit_msg() {
    local task_id="$1"
    local audit_report="${2:-}"

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
        concern=$(_sanitize_audit_title_field "$concern")
        # Lowercase the concern for commit message style
        local concern_lower
        concern_lower=$(echo "$concern" | tr '[:upper:]' '[:lower:]' | sed 's/^[[:space:]]*//')
        echo "$task_id: autofix ${concern_lower}${scope_part}"
    else
        echo "$task_id: automated code improvement"
    fi
}

# Strip list indexes and issue-like markers from audit metadata used in PR
# titles. Autofix cycles are not backed by GitHub issues, so `#123` in PR
# metadata is misleading.
_sanitize_audit_title_field() {
    local value="$1"

    value="$(echo "$value" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')"

    value="$(printf '%s\n' "$value" | sed -E \
        -e 's/^[Ss]pecific[[:space:]]+[Cc]oncern[[:space:]]+#?[0-9]+[[:space:]]*[^[:alnum:]]*[[:space:]]*//' \
        -e 's/^[Gg]eneric[[:space:]]+[Cc]oncern[[:space:]]+#?[0-9]+[[:space:]]*[^[:alnum:]]*[[:space:]]*//' \
        -e 's/^#?[0-9]+[[:space:]]*[^[:alnum:]]*[[:space:]]*//')"

    echo "$value"
}

_sanitize_autofix_pr_text() {
    sed -E \
        -e 's/(\*\*[Cc]oncern\*\*:[[:space:]]*)#[0-9]+[[:space:]]*[^[:alnum:]]*[[:space:]]*/\1/' \
        -e 's/(^|[[:space:]])#[0-9]+[[:space:]]*[^[:alnum:]]+[[:space:]]*/\1/g' \
        -e 's/(^|[[:space:]])#([0-9]+)([^[:alnum:]_]|$)/\1item \2\3/g'
}

_autofix_report_field() {
    local audit_report="$1"
    local label="$2"

    [[ -n "$audit_report" ]] && [[ -f "$audit_report" ]] || return 0
    grep -m1 "^- \\*\\*${label}\\*\\*:" "$audit_report" 2>/dev/null \
        | sed "s/^- \\*\\*${label}\\*\\*: *//" \
        | sed 's/[[:space:]]*$//' \
        || true
}

_autofix_normalize_value() {
    tr '[:upper:]' '[:lower:]' \
        | sed -E 's/[[:space:]]+/ /g; s/^[[:space:]]+//; s/[[:space:]]+$//'
}

_autofix_hash() {
    local content="$1"
    if command -v sha256sum &>/dev/null; then
        printf '%s' "$content" | sha256sum | cut -d' ' -f1
    elif command -v shasum &>/dev/null; then
        printf '%s' "$content" | shasum -a 256 | cut -d' ' -f1
    else
        printf '%s' "$content" | cksum | awk '{print $1}'
    fi
}

_autofix_audit_metadata_json() {
    local audit_report="$1"
    local scope_type scope_target concern_type concern vertical_path normalized_scope_type

    scope_type=$(_autofix_report_field "$audit_report" "Scope type")
    scope_target=$(_autofix_report_field "$audit_report" "Scope target")
    concern_type=$(_autofix_report_field "$audit_report" "Concern type")
    concern=$(_autofix_report_field "$audit_report" "Concern")
    vertical_path=$(_autofix_report_field "$audit_report" "Vertical path")

    concern=$(_sanitize_audit_title_field "$concern")
    normalized_scope_type=$(printf '%s' "$scope_type" | _autofix_normalize_value)
    if [[ "$normalized_scope_type" == global* ]]; then
        scope_target="entire codebase"
    fi

    jq -cn \
        --arg scope_type "$scope_type" \
        --arg scope_target "$scope_target" \
        --arg concern_type "$concern_type" \
        --arg concern "$concern" \
        --arg vertical_path "$vertical_path" \
        '{
            scope_type: $scope_type,
            scope_target: $scope_target,
            concern_type: $concern_type,
            concern: $concern,
            vertical_path: $vertical_path
        }'
}

_autofix_audit_fingerprint() {
    local audit_report="$1"
    local metadata
    metadata=$(_autofix_audit_metadata_json "$audit_report")

    local canonical
    canonical=$(echo "$metadata" | jq -r '
        [
            (.scope_type // "" | ascii_downcase | gsub("\\s+"; " ") | gsub("^\\s+|\\s+$"; "")),
            (.scope_target // "" | ascii_downcase | gsub("\\s+"; " ") | gsub("^\\s+|\\s+$"; "")),
            (.concern_type // "" | ascii_downcase | gsub("\\s+"; " ") | gsub("^\\s+|\\s+$"; "")),
            (.concern // "" | ascii_downcase | gsub("\\s+"; " ") | gsub("^\\s+|\\s+$"; "")),
            (.vertical_path // "" | ascii_downcase | gsub("\\s+"; " ") | gsub("^\\s+|\\s+$"; ""))
        ] | @tsv
    ')

    _autofix_hash "$canonical"
}

_autofix_report_relative_path() {
    local worker_dir="$1"
    local audit_report="${2:-}"

    [[ -n "$audit_report" ]] || return 0
    case "$audit_report" in
        "$worker_dir"/*) echo "${audit_report#"$worker_dir"/}" ;;
        *) echo "$audit_report" ;;
    esac
}

_autofix_dedupe_file() {
    local project_dir="$1"
    local ralph_dir="${RALPH_DIR:-$project_dir/.ralph}"
    echo "$ralph_dir/autofix/dedupe.json"
}

_autofix_remote_duplicate_exists() {
    local fingerprint="$1"
    local title="$2"

    [[ "${WIGGUM_AUTOFIX_REMOTE_DEDUPE:-true}" == "false" ]] && return 1
    command -v gh &>/dev/null || return 1

    local gh_timeout="${WIGGUM_GH_TIMEOUT:-30}"
    local json count

    if [[ -n "$fingerprint" ]]; then
        json=$(timeout "$gh_timeout" gh pr list \
            --state open \
            --limit 100 \
            --search "$fingerprint in:body" \
            --json number 2>/dev/null || true)
        count=$(printf '%s' "$json" | jq 'length' 2>/dev/null || echo 0)
        [[ "$count" =~ ^[0-9]+$ ]] && (( count > 0 )) && return 0
    fi

    if [[ -n "$title" ]]; then
        json=$(timeout "$gh_timeout" gh pr list \
            --state open \
            --limit 100 \
            --json title,number 2>/dev/null || true)
        count=$(printf '%s' "$json" | jq --arg title "$title" '[.[]? | select(.title == $title)] | length' 2>/dev/null || echo 0)
        [[ "$count" =~ ^[0-9]+$ ]] && (( count > 0 )) && return 0
    fi

    return 1
}

_autofix_reserve_audit() {
    local audit_report="$1"
    local worker_dir="$2"
    local project_dir="$3"
    local title="$4"

    local state_file state_dir lock_file fingerprint metadata now ttl cutoff lease_ttl lease_cutoff report_rel worker_id
    state_file=$(_autofix_dedupe_file "$project_dir")
    state_dir=$(dirname "$state_file")
    lock_file="${state_file}.lock"
    mkdir -p "$state_dir"

    fingerprint=$(_autofix_audit_fingerprint "$audit_report")
    metadata=$(_autofix_audit_metadata_json "$audit_report")
    now=$(epoch_now)
    ttl="${WIGGUM_AUTOFIX_DEDUPE_TTL_SECONDS:-604800}"
    [[ "$ttl" =~ ^[0-9]+$ ]] || ttl=604800
    cutoff=$((now - ttl))
    lease_ttl="${WIGGUM_AUTOFIX_RESERVATION_TTL_SECONDS:-21600}"
    [[ "$lease_ttl" =~ ^[0-9]+$ ]] || lease_ttl=21600
    lease_cutoff=$((now - lease_ttl))
    report_rel=$(_autofix_report_relative_path "$worker_dir" "$audit_report")
    worker_id=$(basename "$worker_dir" 2>/dev/null || echo "")

    AUTOFIX_CURRENT_AUDIT_FINGERPRINT="$fingerprint"

    local rc=0
    (
        flock -w 10 200 || exit 3

        if [[ ! -s "$state_file" ]] || ! jq -e . "$state_file" >/dev/null 2>&1; then
            printf '{"version":1,"audits":{}}\n' > "$state_file"
        fi

        if jq -e --arg fp "$fingerprint" --argjson cutoff "$cutoff" --argjson lease_cutoff "$lease_cutoff" '
            (.audits[$fp] // null) as $entry
            | ($entry.status // "") as $status
            | ($entry.updated_at // $entry.created_at // 0) as $updated
            | (
                $entry != null and (
                    ($status == "reserved" and $updated >= $lease_cutoff) or
                    (($status == "pr_created" or $status == "branch_pushed" or $status == "duplicate_remote") and $updated >= $cutoff)
                )
              )
        ' "$state_file" >/dev/null 2>&1; then
            exit 2
        fi

        local tmp_file
        tmp_file=$(mktemp "${state_file}.XXXXXX")
        jq \
            --arg fp "$fingerprint" \
            --arg status "reserved" \
            --arg title "$title" \
            --arg worker "$worker_id" \
            --arg task "${WIGGUM_TASK_ID:-}" \
            --arg report "$report_rel" \
            --argjson metadata "$metadata" \
            --argjson now "$now" \
            --argjson cutoff "$cutoff" '
                .version = 1
                | .audits = (.audits // {} | with_entries(select((.value.updated_at // .value.created_at // 0) >= $cutoff)))
                | .audits[$fp] = ($metadata + {
                    fingerprint: $fp,
                    status: $status,
                    title: $title,
                    worker_id: $worker,
                    task_id: $task,
                    report_file: $report,
                    created_at: $now,
                    updated_at: $now
                })
            ' "$state_file" > "$tmp_file" && mv "$tmp_file" "$state_file"
    ) 200>"$lock_file" || rc=$?

    if [[ "$rc" -ne 0 ]]; then
        return "$rc"
    fi

    if _autofix_remote_duplicate_exists "$fingerprint" "$title"; then
        _autofix_mark_audit_state "$audit_report" "$project_dir" "duplicate_remote" "" ""
        return 2
    fi

    return 0
}

_autofix_mark_audit_state() {
    local audit_report="$1"
    local project_dir="$2"
    local status="$3"
    local branch="${4:-}"
    local pr_url="${5:-}"

    local state_file state_dir lock_file fingerprint now
    state_file=$(_autofix_dedupe_file "$project_dir")
    state_dir=$(dirname "$state_file")
    lock_file="${state_file}.lock"
    mkdir -p "$state_dir"

    fingerprint="${AUTOFIX_CURRENT_AUDIT_FINGERPRINT:-}"
    if [[ -z "$fingerprint" ]]; then
        [[ -n "$audit_report" ]] && [[ -f "$audit_report" ]] || return 0
        fingerprint=$(_autofix_audit_fingerprint "$audit_report")
    fi
    now=$(epoch_now)

    local rc=0
    (
        flock -w 10 200 || exit 3

        if [[ ! -s "$state_file" ]] || ! jq -e . "$state_file" >/dev/null 2>&1; then
            printf '{"version":1,"audits":{}}\n' > "$state_file"
        fi

        local tmp_file
        tmp_file=$(mktemp "${state_file}.XXXXXX")
        jq \
            --arg fp "$fingerprint" \
            --arg status "$status" \
            --arg branch "$branch" \
            --arg pr_url "$pr_url" \
            --argjson now "$now" '
                .version = 1
                | .audits = (.audits // {})
                | .audits[$fp] = ((.audits[$fp] // {fingerprint: $fp, created_at: $now}) + {
                    status: $status,
                    branch: $branch,
                    pr_url: $pr_url,
                    updated_at: $now
                })
            ' "$state_file" > "$tmp_file" && mv "$tmp_file" "$state_file"
    ) 200>"$lock_file" || rc=$?

    return "$rc"
}

# Run a command with exponential backoff retry.
#
# Args:
#   max_attempts - Maximum number of attempts
#   description  - Human-readable description for logging
#   ...          - Command and arguments to run
#
# Returns: exit code from final attempt
_with_backoff() {
    local max_attempts="$1"
    local description="$2"
    shift 2

    local attempt=1
    local delay=2
    local exit_code=0

    while (( attempt <= max_attempts )); do
        exit_code=0
        "$@" 2>&1 || exit_code=$?

        if [[ "$exit_code" -eq 0 ]]; then
            return 0
        fi

        if (( attempt == max_attempts )); then
            log_warn "$description failed after $max_attempts attempts"
            return "$exit_code"
        fi

        log_warn "$description failed (attempt $attempt/$max_attempts), retrying in ${delay}s"
        sleep "$delay"
        (( delay *= 2 ))
        ((++attempt))
    done
}

# Create a per-cycle branch from main, cherry-pick the commit, push, and open a PR.
# Push and PR creation use exponential backoff.
#
# Args:
#   workspace    - Git workspace directory
#   commit_sha   - SHA of the commit on the task branch
#   commit_msg   - Commit message (reused as PR title)
#   worker_dir   - Worker directory
#   project_dir  - Project directory
#   audit_report - Path to the audit report (resolved once by caller)
#
# Returns: 0 if push+PR succeeded, 1 on failure
_push_per_cycle_pr() {
    local workspace="$1"
    local commit_sha="$2"
    local commit_msg="$3"
    local worker_dir="$4"
    local project_dir="${5:-${PROJECT_DIR:-}}"
    local audit_report="${6:-}"

    local default_branch
    default_branch=$(get_default_branch)

    # Fetch latest main
    git -C "$workspace" fetch origin "$default_branch" 2>/dev/null || true

    # Build a slug from the concern for a human-readable branch name
    local cycle_branch
    cycle_branch=$(_make_cycle_branch_name "$audit_report")

    # Save current branch to return to after cherry-pick
    local task_branch
    task_branch=$(git -C "$workspace" rev-parse --abbrev-ref HEAD 2>/dev/null)

    # Create the per-cycle branch from latest main
    local branch_exit=0
    git -C "$workspace" checkout -b "$cycle_branch" "origin/$default_branch" 2>&1 || branch_exit=$?
    if [[ "$branch_exit" -ne 0 ]]; then
        log_warn "Failed to create cycle branch $cycle_branch — falling back to task branch push"
        git -C "$workspace" checkout "$task_branch" 2>/dev/null || true
        _fallback_push "$workspace" "$task_branch" "$commit_msg" "$worker_dir" "$project_dir" "$audit_report"
        return
    fi

    # Cherry-pick the commit onto the per-cycle branch
    local pick_exit=0
    git -C "$workspace" cherry-pick "$commit_sha" --no-gpg-sign 2>&1 || pick_exit=$?
    if [[ "$pick_exit" -ne 0 ]]; then
        log_warn "Cherry-pick onto $cycle_branch failed (conflict with main) — discarding"
        git -C "$workspace" cherry-pick --abort 2>/dev/null || true
        _autofix_mark_audit_state "$audit_report" "$project_dir" "cherry_pick_failed" "$cycle_branch" "" \
            || log_warn "Failed to update autofix dedupe state"
        return 1
    fi

    # Push with exponential backoff (3 attempts: 2s, 4s)
    if ! _with_backoff 3 "Push $cycle_branch" \
        git -C "$workspace" push -u origin "$cycle_branch"; then
        _autofix_mark_audit_state "$audit_report" "$project_dir" "push_failed" "$cycle_branch" "" \
            || log_warn "Failed to update autofix dedupe state"
        return 1
    fi
    log "Pushed to $cycle_branch"

    # Create PR with exponential backoff (3 attempts: 2s, 4s)
    AUTOFIX_LAST_PR_URL=""
    if _with_backoff 3 "Create PR for $cycle_branch" \
        _create_cycle_pr "$workspace" "$cycle_branch" "$commit_msg" "$worker_dir" "$default_branch" "$audit_report"; then
        AUTOFIX_PASS_ACTION="pr_created"
        _autofix_mark_audit_state "$audit_report" "$project_dir" "pr_created" "$cycle_branch" "$AUTOFIX_LAST_PR_URL" \
            || log_warn "Failed to update autofix dedupe state"
    else
        log_warn "PR creation failed — branch was pushed, PR can be created manually"
        AUTOFIX_PASS_ACTION="branch_pushed"
        _autofix_mark_audit_state "$audit_report" "$project_dir" "branch_pushed" "$cycle_branch" "" \
            || log_warn "Failed to update autofix dedupe state"
    fi

    return 0
}

# Generate a branch name for this audit cycle: autofix/<epoch>-<concern-slug>
#
# Args:
#   audit_report - Path to the audit report file (resolved by caller)
#
# Returns: branch name (via stdout)
_make_cycle_branch_name() {
    local audit_report="${1:-}"
    local epoch
    epoch=$(epoch_now)
    local worker_slug
    worker_slug=$(printf '%s' "${WIGGUM_TASK_ID:-autofix}-$$" \
        | tr '[:upper:]' '[:lower:]' \
        | sed 's/[^a-z0-9]/-/g' | sed 's/--*/-/g' | sed 's/^-//;s/-$//' \
        | cut -c1-32)
    [[ -n "$worker_slug" ]] || worker_slug="worker-$$"

    local slug="improvement"
    if [[ -n "$audit_report" ]] && [[ -f "$audit_report" ]]; then
        local concern
        concern=$(grep -m1 '^\- \*\*Concern\*\*:' "$audit_report" 2>/dev/null \
            | sed 's/^- \*\*Concern\*\*: *//' | sed 's/[[:space:]]*$//' || true)
        if [[ -n "$concern" ]]; then
            # Lowercase, replace non-alnum with hyphens, collapse, truncate
            slug=$(echo "$concern" | tr '[:upper:]' '[:lower:]' \
                | sed 's/[^a-z0-9]/-/g' | sed 's/--*/-/g' | sed 's/^-//;s/-$//' \
                | cut -c1-50)
        fi
    fi

    echo "autofix/${epoch}-${worker_slug}-${slug}"
}

# Fallback: push on the existing task branch (used when per-cycle branch fails)
#
# Args:
#   workspace    - Git workspace directory
#   branch       - Branch to push
#   commit_msg   - Commit message (for PR title)
#   worker_dir   - Worker directory
#   project_dir  - Project directory
#   audit_report - Path to the audit report (resolved once by caller)
_fallback_push() {
    local workspace="$1"
    local branch="$2"
    local commit_msg="$3"
    local worker_dir="$4"
    local project_dir="${5:-${PROJECT_DIR:-}}"
    local audit_report="${6:-}"

    if ! _with_backoff 3 "Fallback push $branch" \
        git -C "$workspace" push -u origin "$branch"; then
        # Try force-with-lease as last resort
        if ! _with_backoff 2 "Force push $branch" \
            git -C "$workspace" push --force-with-lease -u origin "$branch"; then
            log_warn "Fallback push failed"
            _autofix_mark_audit_state "$audit_report" "$project_dir" "push_failed" "$branch" "" \
                || log_warn "Failed to update autofix dedupe state"
            return 1
        fi
    fi
    log "Pushed to $branch (fallback)"

    local default_branch
    default_branch=$(get_default_branch)
    AUTOFIX_LAST_PR_URL=""
    if _with_backoff 3 "Create PR for $branch" \
        _create_cycle_pr "$workspace" "$branch" "$commit_msg" "$worker_dir" "$default_branch" "$audit_report"; then
        AUTOFIX_PASS_ACTION="pr_created"
        _autofix_mark_audit_state "$audit_report" "$project_dir" "pr_created" "$branch" "$AUTOFIX_LAST_PR_URL" \
            || log_warn "Failed to update autofix dedupe state"
    else
        log_warn "PR creation failed — branch was pushed, PR can be created manually"
        AUTOFIX_PASS_ACTION="branch_pushed"
        _autofix_mark_audit_state "$audit_report" "$project_dir" "branch_pushed" "$branch" "" \
            || log_warn "Failed to update autofix dedupe state"
    fi
}

# Create a PR for a per-cycle branch with audit context in the body.
#
# Args:
#   workspace      - Git workspace directory
#   branch         - Branch name for the PR
#   commit_msg     - Used as PR title
#   worker_dir     - Worker directory
#   default_branch - Base branch for the PR
#   audit_report   - Path to the audit report (resolved once by caller)
_create_cycle_pr() {
    local workspace="$1"
    local branch="$2"
    local commit_msg="$3"
    local worker_dir="$4"
    local default_branch="$5"
    local audit_report="${6:-}"

    if ! command -v gh &>/dev/null; then
        log_debug "gh CLI not found, skipping PR creation"
        return 1
    fi

    local gh_timeout="${WIGGUM_GH_TIMEOUT:-30}"

    # Build PR body from the pre-resolved audit report
    local body title
    body=$(_build_pr_body "$audit_report")
    title=$(echo "$commit_msg" | _sanitize_autofix_pr_text)

    local pr_output
    pr_output=$(timeout "$gh_timeout" gh pr create \
        --title "$title" \
        --body "$body" \
        --base "$default_branch" \
        --head "$branch" 2>&1) || {
        log_warn "Failed to create PR: ${pr_output:0:200}"
        return 1
    }

    local pr_url
    pr_url=$(timeout "$gh_timeout" gh pr view "$branch" --json url -q '.url' 2>/dev/null || true)
    if [[ -n "$pr_url" ]]; then
        log "Created PR: $pr_url"
        echo "$pr_url" > "$worker_dir/pr_url.txt"
        AUTOFIX_LAST_PR_URL="$pr_url"
    fi
}

# Build a PR body from the audit report.
#
# Args:
#   audit_report - Path to the audit report file (resolved by caller)
#
# Returns: PR body string (via stdout)
_build_pr_body() {
    local audit_report="${1:-}"
    local fingerprint="${AUTOFIX_CURRENT_AUDIT_FINGERPRINT:-}"

    if [[ -n "$fingerprint" ]]; then
        printf '<!-- wiggum-autofix-fingerprint: %s -->\n\n' "$fingerprint"
    fi

    if [[ -n "$audit_report" ]] && [[ -f "$audit_report" ]]; then
        _sanitize_autofix_pr_text < "$audit_report" 2>/dev/null || echo "Autofix code improvement."
    else
        echo "Autofix code improvement."
    fi
}
