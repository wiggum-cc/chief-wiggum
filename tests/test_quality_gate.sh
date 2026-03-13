#!/usr/bin/env bash
# =============================================================================
# Tests for lib/agents/autofix/quality-gate.sh
#
# Tests the shell wrapper that acts on the md agent's gate_result:
#   - PASS: commits changes
#   - FAIL: discards uncommitted changes
#   - Regression: second visit reads current result, not previous FAIL
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

    # Create a real git repo as workspace
    mkdir -p "$TEST_DIR/worker/workspace"
    git -C "$TEST_DIR/worker/workspace" init -b main --quiet
    git -C "$TEST_DIR/worker/workspace" config user.email "test@test.com"
    git -C "$TEST_DIR/worker/workspace" config user.name "Test"

    # Initial commit so we have something to diff against
    echo "initial" > "$TEST_DIR/worker/workspace/file.txt"
    git -C "$TEST_DIR/worker/workspace" add -A
    git -C "$TEST_DIR/worker/workspace" commit -m "initial" --quiet --no-gpg-sign
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

# Helper: source quality-gate.sh agent_run (without md agent loading)
_load_quality_gate() {
    # Define a dummy agent_run that the eval/sed in quality-gate.sh can rename
    agent_run() { :; }

    # Source quality-gate.sh — it renames agent_run to _md_quality_gate_run
    # and defines its own agent_run wrapper
    source "$WIGGUM_HOME/lib/agents/autofix/quality-gate.sh"
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
# Test: PASS keeps changes (commits them)
# =============================================================================
test_pass_commits_changes() {
    export WIGGUM_STEP_ID="quality-gate"
    export _AGENT_START_EPOCH="1000002"

    _load_quality_gate
    _stub_md_agent "PASS"
    _dirty_workspace

    # Stub push to avoid network calls (push will fail, that's ok)
    git() {
        if [[ "${*}" == *"push"* ]]; then
            return 1  # push fails (no remote), but commit should still happen
        fi
        command git "$@"
    }
    export -f git

    agent_run "$TEST_DIR/worker" "$TEST_DIR/project"

    unset -f git

    # Verify the change was committed (workspace is clean, HEAD moved)
    local dirty_after
    dirty_after=$(git -C "$TEST_DIR/worker/workspace" status --porcelain)
    assert_equals "" "$dirty_after" "Workspace should be clean after PASS commit"

    local commit_msg
    commit_msg=$(git -C "$TEST_DIR/worker/workspace" log -1 --format='%s')
    assert_output_contains "$commit_msg" "autofix" "Commit message should contain task ID"
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
    _dirty_workspace

    # Stub push to avoid network calls
    git() {
        if [[ "${*}" == *"push"* ]]; then
            return 1
        fi
        command git "$@"
    }
    export -f git

    agent_run "$TEST_DIR/worker" "$TEST_DIR/project"

    unset -f git

    # The bug: quality-gate used agent_find_latest_result which searched for
    # "*-autofix.quality-gate-result.json" but files are named
    # "*-quality-gate-result.json" (step ID, not agent type).
    # It found nothing, defaulted to FAIL, and discarded changes.
    #
    # With the fix (agent_get_result_path), it reads the correct file.

    # Verify visit 2 committed (not discarded)
    local commit_msg
    commit_msg=$(git -C "$TEST_DIR/worker/workspace" log -1 --format='%s')
    assert_output_contains "$commit_msg" "autofix" \
        "Visit 2: PASS should commit, not discard (regression: must read current result, not previous FAIL)"
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
# Run all tests
# =============================================================================
run_test test_fail_discards_changes
run_test test_pass_commits_changes
run_test test_second_visit_reads_current_result
run_test test_pass_no_changes_is_noop

print_test_summary
exit_with_test_result
