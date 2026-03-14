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
    unset WIGGUM_TASK_ID WIGGUM_STEP_ID _AGENT_START_EPOCH
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

# Helper: stub gh CLI to avoid real GitHub calls
_stub_gh() {
    gh() { return 1; }
    export -f gh
}
_unstub_gh() {
    unset -f gh 2>/dev/null || true
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

    # Verify workspace is back on the task branch at main's HEAD
    local current_branch
    current_branch=$(git -C "$TEST_DIR/worker/workspace" rev-parse --abbrev-ref HEAD 2>/dev/null)
    assert_output_contains "$current_branch" "task/" \
        "Workspace should be back on task branch after per-cycle push"

    # Verify workspace HEAD matches origin/main (reset for next cycle)
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

    local msg
    msg=$(_build_commit_msg "$TEST_DIR/worker" "autofix")
    assert_output_contains "$msg" "stale or misleading comments" \
        "Commit message should include lowercase concern"
    assert_output_contains "$msg" "tests/" \
        "Commit message should include scope target"
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
    msg=$(_build_commit_msg "$TEST_DIR/worker" "autofix")
    assert_equals "autofix: automated code improvement" "$msg" \
        "Commit message should fall back to generic when no report"
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
run_test test_commit_msg_fallback_no_report
run_test test_artifact_cleanup

print_test_summary
exit_with_test_result
