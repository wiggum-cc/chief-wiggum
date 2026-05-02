#!/usr/bin/env bash
# =============================================================================
# Tests for lib/agents/autofix/quality-gate.sh
#
# Tests the shell wrapper that acts on the md agent's gate_result:
#   - PASS: commits changes, creates per-cycle branch + PR
#   - FAIL: discards uncommitted changes
#   - Regression: second visit reads current result, not previous FAIL
#   - Per-cycle branch: cherry-picks onto branch from main, resets workspace
#   - Commit message: includes audit scope/concern from report
#   - Artifact cleanup: removes temp files before commit
# =============================================================================

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

TEST_DIR=""

# Source core dependencies
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_source_core
source "$WIGGUM_HOME/lib/git/git-operations.sh"
[ -z "${_WIGGUM_SRC_PLATFORM_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/agent-result.sh"

setup() {
    TEST_DIR=$(mktemp -d)
    export LOG_FILE="/dev/null"
    export WIGGUM_TASK_ID="autofix"

    # Create worker structure
    mkdir -p "$TEST_DIR/worker/results" "$TEST_DIR/worker/logs" "$TEST_DIR/worker/reports"
    mkdir -p "$TEST_DIR/project"
    export RALPH_DIR="$TEST_DIR/project/.ralph"
    mkdir -p "$RALPH_DIR"

    # Create a bare remote repo so push/fetch/origin work
    git init --bare --quiet "$TEST_DIR/remote.git"

    # Create workspace cloned from the remote
    git clone --quiet "$TEST_DIR/remote.git" "$TEST_DIR/worker/workspace"
    git -C "$TEST_DIR/worker/workspace" config user.email "test@test.com"
    git -C "$TEST_DIR/worker/workspace" config user.name "Test"

    # Initial commit so we have something to diff against
    echo "initial" > "$TEST_DIR/worker/workspace/file.txt"
    git -C "$TEST_DIR/worker/workspace" add -A
    git -C "$TEST_DIR/worker/workspace" commit -m "initial" --quiet --no-gpg-sign
    git -C "$TEST_DIR/worker/workspace" push --quiet origin main

    # Create a task branch (mimics worktree-helpers.sh setup)
    git -C "$TEST_DIR/worker/workspace" checkout -b "task/autofix-1000000" --quiet
}

teardown() {
    unset WIGGUM_TASK_ID WIGGUM_STEP_ID _AGENT_START_EPOCH RALPH_DIR WIGGUM_AUTOFIX_REMOTE_DEDUPE
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# Helper: write a result file the way the md agent would
_write_result() {
    local worker_dir="$1"
    local gate_result="$2"
    local epoch="${_AGENT_START_EPOCH:-$(date +%s)}"
    local step_id="${WIGGUM_STEP_ID:-quality-gate}"

    mkdir -p "$worker_dir/results"
    cat > "$worker_dir/results/${epoch}-${step_id}-result.json" << EOF
{"outputs": {"gate_result": "$gate_result"}}
EOF
}

# Helper: stub _md_quality_gate_run to write a result and return
_stub_md_agent() {
    local result="$1"
    eval "_md_quality_gate_run() {
        local worker_dir=\"\$1\"
        _write_result \"\$worker_dir\" \"$result\"
        return 0
    }"
}

# Helper: add uncommitted changes to workspace
_dirty_workspace() {
    echo "modified-$(date +%s%N)" > "$TEST_DIR/worker/workspace/file.txt"
}

# Helper: write a fake random-audit report with scope/concern
_write_audit_report() {
    local worker_dir="$1"
    local scope_target="${2:-lib/core/}"
    local concern="${3:-Race conditions and concurrency bugs}"
    local epoch="${_AGENT_START_EPOCH:-$(date +%s)}"

    mkdir -p "$worker_dir/reports"
    cat > "$worker_dir/reports/${epoch}-random-audit-report.md" << EOF
## Audit Parameters

- **Scope type**: Focused
- **Scope target**: ${scope_target}
- **Concern type**: Specific
- **Concern**: ${concern}
- **Selection method**: shuf -i 1-10 -n 1

## Findings

### [HIGH] F001
- **Location**: lib/core/foo.sh:42
- **Issue**: Potential race condition
EOF
}

# Helper: source quality-gate.sh agent_run (without md agent loading)
_load_quality_gate() {
    # Define a dummy agent_run that the eval/sed in quality-gate.sh can rename
    agent_run() { :; }

    # Source quality-gate.sh — it renames agent_run to _md_quality_gate_run
    # and defines its own agent_run wrapper
    source "$WIGGUM_HOME/lib/agents/autofix/quality-gate.sh"
}

# Helper: stub gh CLI to avoid real GitHub calls.
# Creates a fake gh script on PATH so that `timeout ... gh` and
# `command -v gh` both find the stub instead of the real binary.
# The stub succeeds (exit 0) to avoid triggering backoff retries.
_stub_gh() {
    _GH_STUB_DIR=$(mktemp -d)
    cat > "$_GH_STUB_DIR/gh" << 'STUB'
#!/usr/bin/env bash
# Stub: print a fake PR URL for `gh pr create`, empty for others
if [[ "${1:-}" == "pr" && "${2:-}" == "create" ]]; then
    echo "https://github.com/test/test/pull/1"
elif [[ "${1:-}" == "pr" && "${2:-}" == "view" ]]; then
    echo '{"url":"https://github.com/test/test/pull/1"}'
fi
exit 0
STUB
    chmod +x "$_GH_STUB_DIR/gh"
    _GH_OLD_PATH="$PATH"
    export PATH="$_GH_STUB_DIR:$PATH"
}
_unstub_gh() {
    if [[ -n "${_GH_OLD_PATH:-}" ]]; then
        export PATH="$_GH_OLD_PATH"
        unset _GH_OLD_PATH
    fi
    [[ -n "${_GH_STUB_DIR:-}" ]] && rm -rf "$_GH_STUB_DIR"
    unset _GH_STUB_DIR
}

# =============================================================================
# Test: FAIL discards uncommitted changes
# =============================================================================
test_fail_discards_changes() {
    export WIGGUM_STEP_ID="quality-gate"
    export _AGENT_START_EPOCH="1000001"

    _load_quality_gate
    _stub_md_agent "FAIL"
    _dirty_workspace

    # Verify workspace is dirty
    local dirty_before
    dirty_before=$(git -C "$TEST_DIR/worker/workspace" status --porcelain)
    assert_not_empty "$dirty_before" "Workspace should be dirty before quality gate"

    agent_run "$TEST_DIR/worker" "$TEST_DIR/project"

    # Verify workspace is clean after FAIL
    local dirty_after
    dirty_after=$(git -C "$TEST_DIR/worker/workspace" status --porcelain)
    assert_equals "" "$dirty_after" "Workspace should be clean after FAIL"
}

# =============================================================================
# Test: PASS commits and creates per-cycle branch from main
# =============================================================================
test_pass_creates_per_cycle_branch() {
    export WIGGUM_STEP_ID="quality-gate"
    export _AGENT_START_EPOCH="1000002"

    _load_quality_gate
    _stub_md_agent "PASS"
    _stub_gh
    _dirty_workspace
    _write_audit_report "$TEST_DIR/worker"

    agent_run "$TEST_DIR/worker" "$TEST_DIR/project"

    _unstub_gh

    # Verify a per-cycle branch was created on the remote
    local remote_branches
    remote_branches=$(git -C "$TEST_DIR/remote.git" branch --list 'autofix/*' 2>/dev/null)
    assert_not_empty "$remote_branches" "Per-cycle autofix branch should exist on remote"

    # Verify the per-cycle branch name contains the concern slug
    assert_output_contains "$remote_branches" "race-conditions" \
        "Branch name should contain concern slug"

    # Verify workspace HEAD matches origin/main (reset for next cycle).
    # Uses detached HEAD to avoid worktree branch contention, so we check
    # commit SHA rather than branch name.
    local workspace_head main_head
    workspace_head=$(git -C "$TEST_DIR/worker/workspace" rev-parse HEAD)
    main_head=$(git -C "$TEST_DIR/worker/workspace" rev-parse origin/main)
    assert_equals "$main_head" "$workspace_head" \
        "Workspace should be reset to origin/main for next cycle"
}

# =============================================================================
# Test: Per-cycle branch contains the commit with correct message
# =============================================================================
test_per_cycle_branch_has_correct_commit() {
    export WIGGUM_STEP_ID="quality-gate"
    export _AGENT_START_EPOCH="1000003"

    _load_quality_gate
    _stub_md_agent "PASS"
    _stub_gh
    _dirty_workspace
    _write_audit_report "$TEST_DIR/worker" "lib/core/" "Race conditions and concurrency bugs"

    agent_run "$TEST_DIR/worker" "$TEST_DIR/project"

    _unstub_gh

    # Find the per-cycle branch
    local cycle_branch
    cycle_branch=$(git -C "$TEST_DIR/remote.git" branch --list 'autofix/*' | tr -d ' ' | head -1)

    # Check the commit message on the per-cycle branch
    local commit_msg
    commit_msg=$(git -C "$TEST_DIR/worker/workspace" log -1 --format='%s' "origin/$cycle_branch" 2>/dev/null)
    assert_output_contains "$commit_msg" "race conditions" \
        "Commit message should include the concern"
    assert_output_contains "$commit_msg" "lib/core/" \
        "Commit message should include the scope target"
}

# =============================================================================
# Test: Second visit reads current PASS, not previous FAIL (the bug)
# =============================================================================
test_second_visit_reads_current_result() {
    export WIGGUM_STEP_ID="quality-gate"

    _load_quality_gate

    # --- Visit 1: FAIL ---
    export _AGENT_START_EPOCH="2000001"
    _stub_md_agent "FAIL"
    _dirty_workspace

    agent_run "$TEST_DIR/worker" "$TEST_DIR/project"

    # Verify visit 1 discarded changes
    local dirty_v1
    dirty_v1=$(git -C "$TEST_DIR/worker/workspace" status --porcelain)
    assert_equals "" "$dirty_v1" "Visit 1: workspace should be clean after FAIL"

    # Verify FAIL result file exists
    assert_file_exists "$TEST_DIR/worker/results/2000001-quality-gate-result.json" \
        "Visit 1 result file should exist"

    # --- Visit 2: PASS ---
    export _AGENT_START_EPOCH="2000002"
    _stub_md_agent "PASS"
    _stub_gh
    _dirty_workspace

    agent_run "$TEST_DIR/worker" "$TEST_DIR/project"

    _unstub_gh

    # The bug: quality-gate used agent_find_latest_result which searched for
    # "*-autofix.quality-gate-result.json" but files are named
    # "*-quality-gate-result.json" (step ID, not agent type).
    # It found nothing, defaulted to FAIL, and discarded changes.
    #
    # With the fix (agent_get_result_path), it reads the correct file.

    # Verify visit 2 created a per-cycle branch (commit was not discarded)
    local remote_branches
    remote_branches=$(git -C "$TEST_DIR/remote.git" branch --list 'autofix/*' 2>/dev/null)
    assert_not_empty "$remote_branches" \
        "Visit 2: PASS should create per-cycle branch, not discard (regression: must read current result)"
}

# =============================================================================
# Test: PASS with no changes is a no-op
# =============================================================================
test_pass_no_changes_is_noop() {
    export WIGGUM_STEP_ID="quality-gate"
    export _AGENT_START_EPOCH="3000001"

    _load_quality_gate
    _stub_md_agent "PASS"

    # Don't dirty the workspace

    local head_before
    head_before=$(git -C "$TEST_DIR/worker/workspace" rev-parse HEAD)

    agent_run "$TEST_DIR/worker" "$TEST_DIR/project"

    local head_after
    head_after=$(git -C "$TEST_DIR/worker/workspace" rev-parse HEAD)

    assert_equals "$head_before" "$head_after" "PASS with no changes should not create a commit"
}

# =============================================================================
# Test: Commit message includes audit scope when report exists
# =============================================================================
test_commit_msg_includes_audit_scope() {
    export WIGGUM_STEP_ID="quality-gate"
    export _AGENT_START_EPOCH="4000001"

    _load_quality_gate

    _write_audit_report "$TEST_DIR/worker" "tests/" "Stale or misleading comments"

    local audit_report
    audit_report=$(agent_find_latest_report "$TEST_DIR/worker" "random-audit")

    local msg
    msg=$(_build_commit_msg "autofix" "$audit_report")
    assert_output_contains "$msg" "stale or misleading comments" \
        "Commit message should include lowercase concern"
    assert_output_contains "$msg" "tests/" \
        "Commit message should include scope target"
}

test_commit_msg_strips_issue_reference_from_concern() {
    export WIGGUM_STEP_ID="quality-gate"
    export _AGENT_START_EPOCH="4000003"

    _load_quality_gate

    _write_audit_report "$TEST_DIR/worker" "packages/" "#41 — Incorrect escaping or quoting in generated code"

    local audit_report
    audit_report=$(agent_find_latest_report "$TEST_DIR/worker" "random-audit")

    local msg
    msg=$(_build_commit_msg "autofix" "$audit_report")
    assert_output_not_contains "$msg" "#41" \
        "Commit/PR title should not contain issue-reference shorthand"
    assert_output_contains "$msg" "incorrect escaping or quoting" \
        "Commit/PR title should keep the concern text"
}

test_pr_body_strips_issue_reference_shorthand() {
    export WIGGUM_STEP_ID="quality-gate"
    export _AGENT_START_EPOCH="4000004"

    _load_quality_gate

    _write_audit_report "$TEST_DIR/worker" "packages/" "#54 — Sensitive data in log output"
    cat >> "$TEST_DIR/worker/reports/4000004-random-audit-report.md" << 'EOF'
- **Issue**: Finding #1 leaks tokens
EOF

    local audit_report
    audit_report=$(agent_find_latest_report "$TEST_DIR/worker" "random-audit")

    local body
    body=$(_build_pr_body "$audit_report")
    assert_output_not_contains "$body" "#54" \
        "PR body should not contain issue-reference shorthand for concerns"
    assert_output_not_contains "$body" "#1" \
        "PR body should not contain issue-reference shorthand for findings"
    assert_output_contains "$body" "Sensitive data in log output" \
        "PR body should keep concern text"
}

# =============================================================================
# Test: Commit message falls back when no report exists
# =============================================================================
test_commit_msg_fallback_no_report() {
    export WIGGUM_STEP_ID="quality-gate"
    export _AGENT_START_EPOCH="4000002"

    _load_quality_gate

    # No audit report written

    local msg
    msg=$(_build_commit_msg "autofix" "")
    assert_equals "autofix: automated code improvement" "$msg" \
        "Commit message should fall back to generic when no report"
}

test_resolve_cycle_audit_report_uses_verify_parent() {
    export WIGGUM_STEP_ID="quality-gate"
    export _AGENT_START_EPOCH="4100001"

    _load_quality_gate

    mkdir -p "$TEST_DIR/worker/reports" "$TEST_DIR/worker/results"

    cat > "$TEST_DIR/worker/reports/4100001-random-audit-report.md" << 'EOF'
## Audit Parameters

- **Scope type**: Focused
- **Scope target**: simulation/
- **Concern type**: Specific
- **Concern**: Unchecked return values from system calls or library functions
EOF

    cat > "$TEST_DIR/worker/reports/4100002-random-audit-report.md" << 'EOF'
## Audit Parameters

- **Scope type**: Focused
- **Scope target**: lib/
- **Concern type**: Specific
- **Concern**: Race conditions and concurrency bugs
EOF

    cat > "$TEST_DIR/worker/results/4100003-verify-fix-result.json" << 'EOF'
{"outputs":{"gate_result":"PASS","parent_report_file":"reports/4100001-random-audit-report.md"}}
EOF

    local audit_report msg
    audit_report=$(_resolve_cycle_audit_report "$TEST_DIR/worker")
    msg=$(_build_commit_msg "autofix-w2" "$audit_report")

    assert_equals "$TEST_DIR/worker/reports/4100001-random-audit-report.md" "$audit_report" \
        "Quality gate should use the audit report consumed by verify-fix"
    assert_output_contains "$msg" "unchecked return values" \
        "Commit message should come from verify-fix parent report"
    assert_output_not_contains "$msg" "race conditions" \
        "Commit message should not use a later random-audit report"
}

test_autofix_reserve_deduplicates_same_audit() {
    export WIGGUM_STEP_ID="quality-gate"
    export _AGENT_START_EPOCH="4200001"
    export WIGGUM_AUTOFIX_REMOTE_DEDUPE=false

    _load_quality_gate
    _write_audit_report "$TEST_DIR/worker" "simulation/" "Unchecked return values from system calls or library functions"

    local audit_report title first_rc second_rc fingerprint_count
    audit_report=$(agent_find_latest_report "$TEST_DIR/worker" "random-audit")
    title=$(_build_commit_msg "autofix-w2" "$audit_report")

    first_rc=0
    _autofix_reserve_audit "$audit_report" "$TEST_DIR/worker" "$TEST_DIR/project" "$title" || first_rc=$?
    second_rc=0
    _autofix_reserve_audit "$audit_report" "$TEST_DIR/worker" "$TEST_DIR/project" "$title" || second_rc=$?

    fingerprint_count=$(jq '.audits | length' "$TEST_DIR/project/.ralph/autofix/dedupe.json")

    assert_equals "0" "$first_rc" "First audit reservation should succeed"
    assert_equals "2" "$second_rc" "Second identical audit reservation should be classified as duplicate"
    assert_equals "1" "$fingerprint_count" "Dedupe ledger should contain one fingerprint"

    unset WIGGUM_AUTOFIX_REMOTE_DEDUPE
}

test_duplicate_audit_pass_skips_pr_creation() {
    export WIGGUM_STEP_ID="quality-gate"
    export _AGENT_START_EPOCH="4300001"
    export WIGGUM_AUTOFIX_REMOTE_DEDUPE=false

    _load_quality_gate
    _stub_md_agent "PASS"
    _stub_gh
    _dirty_workspace
    _write_audit_report "$TEST_DIR/worker" "simulation/" "Unchecked return values from system calls or library functions"

    local audit_report title reserve_rc
    audit_report=$(agent_find_latest_report "$TEST_DIR/worker" "random-audit")
    title=$(_build_commit_msg "autofix-w2" "$audit_report")
    reserve_rc=0
    _autofix_reserve_audit "$audit_report" "$TEST_DIR/worker" "$TEST_DIR/project" "$title" || reserve_rc=$?

    agent_run "$TEST_DIR/worker" "$TEST_DIR/project"

    _unstub_gh

    local remote_branches dirty_after
    remote_branches=$(git -C "$TEST_DIR/remote.git" branch --list 'autofix/*' 2>/dev/null)
    dirty_after=$(git -C "$TEST_DIR/worker/workspace" status --porcelain)

    assert_equals "0" "$reserve_rc" "Precondition reservation should succeed"
    assert_equals "" "$remote_branches" "Duplicate audit should not create another autofix branch"
    assert_equals "" "$dirty_after" "Duplicate audit should be discarded after quality gate reset"

    unset WIGGUM_AUTOFIX_REMOTE_DEDUPE
}

# =============================================================================
# Test: Artifact cleanup removes temp files before commit
# =============================================================================
test_artifact_cleanup() {
    export WIGGUM_STEP_ID="quality-gate"
    export _AGENT_START_EPOCH="5000001"

    _load_quality_gate
    _stub_md_agent "PASS"
    _stub_gh
    _dirty_workspace

    # Create artifact files that should be cleaned
    touch "$TEST_DIR/worker/workspace/debug.tmp"
    touch "$TEST_DIR/worker/workspace/old.bak"
    mkdir -p "$TEST_DIR/worker/workspace/__pycache__"
    touch "$TEST_DIR/worker/workspace/__pycache__/foo.pyc"

    agent_run "$TEST_DIR/worker" "$TEST_DIR/project"

    _unstub_gh

    # Verify artifacts were cleaned (not committed)
    local cycle_branch
    cycle_branch=$(git -C "$TEST_DIR/remote.git" branch --list 'autofix/*' | tr -d ' ' | head -1)

    if [[ -n "$cycle_branch" ]]; then
        # Check the committed tree doesn't contain artifacts
        local tree_files
        tree_files=$(git -C "$TEST_DIR/worker/workspace" ls-tree -r --name-only "origin/$cycle_branch" 2>/dev/null)
        local has_artifacts=""
        if echo "$tree_files" | grep -qE '\.tmp$|\.bak$|__pycache__'; then
            has_artifacts="found"
        fi
        assert_equals "" "$has_artifacts" "Artifacts should not be in the committed tree"
    fi

    # Verify the local artifacts were deleted
    assert_file_not_exists "$TEST_DIR/worker/workspace/debug.tmp" \
        "debug.tmp should be cleaned up"
    assert_file_not_exists "$TEST_DIR/worker/workspace/old.bak" \
        "old.bak should be cleaned up"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_fail_discards_changes
run_test test_pass_creates_per_cycle_branch
run_test test_per_cycle_branch_has_correct_commit
run_test test_second_visit_reads_current_result
run_test test_pass_no_changes_is_noop
run_test test_commit_msg_includes_audit_scope
run_test test_commit_msg_strips_issue_reference_from_concern
run_test test_pr_body_strips_issue_reference_shorthand
run_test test_commit_msg_fallback_no_report
run_test test_resolve_cycle_audit_report_uses_verify_parent
run_test test_autofix_reserve_deduplicates_same_audit
run_test test_duplicate_audit_pass_skips_pr_creation
run_test test_artifact_cleanup

print_test_summary
exit_with_test_result
