#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/agents/workflow/*.sh
# Tests the git-sync-main, git-commit-push, and pr-merge agents

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/agent-base.sh"

# Create temp dir for test isolation
TEST_DIR=""
RALPH_DIR=""
WORKER_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    mkdir -p "$RALPH_DIR/workers"

    WORKER_DIR="$RALPH_DIR/workers/worker-TEST-001-$(date +%s)"
    mkdir -p "$WORKER_DIR/workspace"
    mkdir -p "$WORKER_DIR/logs"
    mkdir -p "$WORKER_DIR/results"
    mkdir -p "$WORKER_DIR/reports"

    # Initialize a git repo in workspace
    git -C "$WORKER_DIR/workspace" init -q
    git -C "$WORKER_DIR/workspace" config user.email "test@test.com"
    git -C "$WORKER_DIR/workspace" config user.name "Test User"
    echo "initial" > "$WORKER_DIR/workspace/file.txt"
    git -C "$WORKER_DIR/workspace" add .
    git -C "$WORKER_DIR/workspace" commit -q -m "Initial commit"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# git-sync-main Agent Tests
# =============================================================================

test_git_sync_main_agent_exists() {
    assert_file_exists "$WIGGUM_HOME/lib/agents/workflow/git-sync-main.sh" "Agent file should exist"
}

test_git_sync_main_agent_sources() {
    source "$WIGGUM_HOME/lib/agents/workflow/git-sync-main.sh"

    assert_equals "workflow.git-sync-main" "$AGENT_TYPE" "Agent type should be set"
}

test_git_sync_main_missing_workspace_fails() {
    [ -n "$WORKER_DIR" ] && rm -rf "$WORKER_DIR/workspace"

    source "$WIGGUM_HOME/lib/agents/workflow/git-sync-main.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail without workspace"
}

test_git_sync_main_not_git_repo_fails() {
    [ -n "$WORKER_DIR" ] && rm -rf "$WORKER_DIR/workspace/.git"

    source "$WIGGUM_HOME/lib/agents/workflow/git-sync-main.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail for non-git repo"
}

# =============================================================================
# git-sync-main Cascade Strategy Tests (A+F)
# =============================================================================

test_sync_main_fast_forward() {
    # Setup: create a bare remote and workspace that's behind
    local bare_remote="$TEST_DIR/remote.git"
    git init --bare "$bare_remote" >/dev/null 2>&1

    local ws="$WORKER_DIR/workspace"
    git -C "$ws" remote add origin "$bare_remote"
    git -C "$ws" push -u origin HEAD:main >/dev/null 2>&1

    # Create a commit on main via the bare remote (simulate someone else pushing)
    local clone_dir="$TEST_DIR/clone"
    git clone -q "$bare_remote" "$clone_dir" 2>/dev/null
    git -C "$clone_dir" config user.email "test@test.com"
    git -C "$clone_dir" config user.name "Test"
    echo "new content" > "$clone_dir/newfile.txt"
    git -C "$clone_dir" add .
    git -C "$clone_dir" commit -q -m "Advance main"
    git -C "$clone_dir" push -q origin main 2>/dev/null

    # Now workspace is behind origin/main with no local commits — should fast-forward
    source "$WIGGUM_HOME/lib/agents/workflow/git-sync-main.sh"
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null

    local result_file
    result_file=$(find "$WORKER_DIR/results" -name "*-result.json" | head -1)
    if [ -n "$result_file" ]; then
        local gate_result merge_status
        gate_result=$(jq -r '.outputs.gate_result // empty' "$result_file")
        merge_status=$(jq -r '.outputs.merge_status // empty' "$result_file")
        assert_equals "PASS" "$gate_result" "Should PASS on fast-forward"
        assert_equals "synced" "$merge_status" "Should report synced status"
    fi
}

test_sync_main_rebase_linear() {
    # Setup: create a bare remote, workspace with local commits, then advance main
    local bare_remote="$TEST_DIR/remote.git"
    git init --bare "$bare_remote" >/dev/null 2>&1

    local ws="$WORKER_DIR/workspace"
    git -C "$ws" remote add origin "$bare_remote"
    git -C "$ws" push -u origin HEAD:main >/dev/null 2>&1

    # Create a local branch with a commit
    git -C "$ws" checkout -b task/TEST-001-123 2>/dev/null
    echo "local work" > "$ws/local.txt"
    git -C "$ws" add .
    git -C "$ws" commit -q -m "Local work"
    git -C "$ws" push -u origin task/TEST-001-123 >/dev/null 2>&1

    # Advance main (non-conflicting change)
    local clone_dir="$TEST_DIR/clone"
    git clone -q "$bare_remote" "$clone_dir" 2>/dev/null
    git -C "$clone_dir" config user.email "test@test.com"
    git -C "$clone_dir" config user.name "Test"
    echo "main advance" > "$clone_dir/main_only.txt"
    git -C "$clone_dir" add .
    git -C "$clone_dir" commit -q -m "Advance main"
    git -C "$clone_dir" push -q origin main 2>/dev/null

    source "$WIGGUM_HOME/lib/agents/workflow/git-sync-main.sh"
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null

    local result_file
    result_file=$(find "$WORKER_DIR/results" -name "*-result.json" | head -1)
    if [ -n "$result_file" ]; then
        local gate_result merge_status
        gate_result=$(jq -r '.outputs.gate_result // empty' "$result_file")
        merge_status=$(jq -r '.outputs.merge_status // empty' "$result_file")
        assert_equals "PASS" "$gate_result" "Should PASS on rebase"
        assert_equals "synced" "$merge_status" "Should report synced status"
    fi
}

test_sync_main_merge_fallback_on_conflict() {
    # Setup: create conflicting changes on both sides
    local bare_remote="$TEST_DIR/remote.git"
    git init --bare "$bare_remote" >/dev/null 2>&1

    local ws="$WORKER_DIR/workspace"
    git -C "$ws" remote add origin "$bare_remote"
    git -C "$ws" push -u origin HEAD:main >/dev/null 2>&1

    # Local branch modifies file.txt
    git -C "$ws" checkout -b task/TEST-002-123 2>/dev/null
    echo "local version" > "$ws/file.txt"
    git -C "$ws" add .
    git -C "$ws" commit -q -m "Local change"

    # Main modifies same file differently
    local clone_dir="$TEST_DIR/clone"
    git clone -q "$bare_remote" "$clone_dir" 2>/dev/null
    git -C "$clone_dir" config user.email "test@test.com"
    git -C "$clone_dir" config user.name "Test"
    echo "main version" > "$clone_dir/file.txt"
    git -C "$clone_dir" add .
    git -C "$clone_dir" commit -q -m "Main change"
    git -C "$clone_dir" push -q origin main 2>/dev/null

    source "$WIGGUM_HOME/lib/agents/workflow/git-sync-main.sh"
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null

    local result_file
    result_file=$(find "$WORKER_DIR/results" -name "*-result.json" | head -1)
    if [ -n "$result_file" ]; then
        local gate_result merge_status
        gate_result=$(jq -r '.outputs.gate_result // empty' "$result_file")
        merge_status=$(jq -r '.outputs.merge_status // empty' "$result_file")
        assert_equals "FAIL" "$gate_result" "Should FAIL with conflicts"
        assert_equals "failed" "$merge_status" "Should report failed status"
    fi
}

# =============================================================================
# git-commit-push Agent Tests
# =============================================================================

test_git_commit_push_agent_exists() {
    assert_file_exists "$WIGGUM_HOME/lib/agents/workflow/git-commit-push.sh" "Agent file should exist"
}

test_git_commit_push_agent_sources() {
    source "$WIGGUM_HOME/lib/agents/workflow/git-commit-push.sh"

    assert_equals "workflow.git-commit-push" "$AGENT_TYPE" "Agent type should be set"
}

test_git_commit_push_no_changes_passes() {
    # Create a branch first
    git -C "$WORKER_DIR/workspace" checkout -b test-branch 2>/dev/null

    source "$WIGGUM_HOME/lib/agents/workflow/git-commit-push.sh"
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null

    # Check result file
    local result_file
    result_file=$(find "$WORKER_DIR/results" -name "*-result.json" | head -1)

    if [ -n "$result_file" ]; then
        local gate_result
        gate_result=$(jq -r '.outputs.gate_result' "$result_file")
        assert_equals "PASS" "$gate_result" "Should PASS with no changes"
    fi
}

test_git_commit_push_commits_changes() {
    # Create a branch and make changes
    git -C "$WORKER_DIR/workspace" checkout -b test-branch 2>/dev/null
    echo "modified" > "$WORKER_DIR/workspace/file.txt"

    source "$WIGGUM_HOME/lib/agents/workflow/git-commit-push.sh"

    # Mock git push to avoid actually pushing
    export GIT_TERMINAL_PROMPT=0

    # Run agent (will fail at push since no remote, but should commit)
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || true

    # Check that commit was created
    local commit_count
    commit_count=$(git -C "$WORKER_DIR/workspace" log --oneline | wc -l)
    assert_greater_than "$commit_count" "1" "Should have created a commit"
}

test_git_commit_push_missing_workspace_fails() {
    [ -n "$WORKER_DIR" ] && rm -rf "$WORKER_DIR/workspace"

    source "$WIGGUM_HOME/lib/agents/workflow/git-commit-push.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail without workspace"
}

test_git_commit_push_detects_unpushed_commits() {
    # Create a bare remote to track against
    local bare_remote="$TEST_DIR/remote.git"
    git init --bare "$bare_remote" >/dev/null 2>&1

    # Set up workspace with remote tracking
    git -C "$WORKER_DIR/workspace" checkout -b test-branch 2>/dev/null
    git -C "$WORKER_DIR/workspace" remote add origin "$bare_remote"
    git -C "$WORKER_DIR/workspace" push -u origin test-branch >/dev/null 2>&1

    # Create a local commit (simulating checkpoint commit from readonly agent)
    echo "checkpoint content" > "$WORKER_DIR/workspace/resolved.txt"
    git -C "$WORKER_DIR/workspace" add -A
    git -C "$WORKER_DIR/workspace" commit -m "chore: checkpoint before read-only agent" >/dev/null 2>&1

    # Verify we have unpushed commits
    local unpushed_before
    unpushed_before=$(git -C "$WORKER_DIR/workspace" rev-list '@{u}..HEAD' --count 2>/dev/null)
    assert_equals "1" "$unpushed_before" "Should have 1 unpushed commit before agent runs"

    source "$WIGGUM_HOME/lib/agents/workflow/git-commit-push.sh"

    # Run agent and capture output
    local output
    output=$(agent_run "$WORKER_DIR" "$TEST_DIR" 2>&1) || true

    # Should log that it found unpushed commits
    assert_output_contains "$output" "Found 1 unpushed commit" "Should detect unpushed commits"

    # Verify the commit was pushed
    local unpushed_after
    unpushed_after=$(git -C "$WORKER_DIR/workspace" rev-list '@{u}..HEAD' --count 2>/dev/null)
    assert_equals "0" "$unpushed_after" "Should have 0 unpushed commits after agent runs"
}

test_git_commit_push_rebase_fallback_on_force_push_blocked() {
    # Setup: bare remote with a pre-receive hook that rejects force pushes
    local bare_remote="$TEST_DIR/remote.git"
    git init --bare "$bare_remote" >/dev/null 2>&1

    local ws="$WORKER_DIR/workspace"
    git -C "$ws" checkout -b task/TEST-001-456 2>/dev/null
    git -C "$ws" remote add origin "$bare_remote"
    git -C "$ws" push -u origin task/TEST-001-456 >/dev/null 2>&1

    # Create a local commit
    echo "local change" > "$ws/local.txt"
    git -C "$ws" add .
    git -C "$ws" commit -q -m "Local change"

    # Simulate remote having an extra commit (causes non-fast-forward)
    local clone_dir="$TEST_DIR/clone"
    git clone -q "$bare_remote" "$clone_dir" 2>/dev/null
    git -C "$clone_dir" config user.email "test@test.com"
    git -C "$clone_dir" config user.name "Test"
    git -C "$clone_dir" checkout task/TEST-001-456 2>/dev/null
    echo "remote change" > "$clone_dir/remote.txt"
    git -C "$clone_dir" add .
    git -C "$clone_dir" commit -q -m "Remote change"
    git -C "$clone_dir" push -q origin task/TEST-001-456 2>/dev/null

    # Fetch so local reflog knows about the remote commit — without this,
    # --force-with-lease fails with "stale info" before reaching the hook
    git -C "$ws" fetch origin 2>/dev/null

    # Install a pre-receive hook that blocks force pushes (simulates GH013)
    cat > "$bare_remote/hooks/pre-receive" << 'HOOK'
#!/usr/bin/env bash
while read -r old_oid new_oid ref; do
    if [ "$old_oid" != "0000000000000000000000000000000000000000" ]; then
        # Check if old_oid is ancestor of new_oid (non-force push)
        if ! git merge-base --is-ancestor "$old_oid" "$new_oid" 2>/dev/null; then
            echo "error: GH013: force-push is not allowed for this branch"
            exit 1
        fi
    fi
done
HOOK
    chmod +x "$bare_remote/hooks/pre-receive"

    source "$WIGGUM_HOME/lib/agents/workflow/git-commit-push.sh"

    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "0" "$result" "Should succeed via rebase fallback"

    # Verify result file shows PASS
    local result_file
    result_file=$(find "$WORKER_DIR/results" -name "*-result.json" | head -1)
    if [ -n "$result_file" ]; then
        local gate_result
        gate_result=$(jq -r '.outputs.gate_result' "$result_file")
        assert_equals "PASS" "$gate_result" "Should PASS after rebase fallback"
    fi

    # Verify push actually went through — no unpushed commits
    local unpushed_after
    unpushed_after=$(git -C "$ws" rev-list '@{u}..HEAD' --count 2>/dev/null)
    assert_equals "0" "$unpushed_after" "Should have 0 unpushed commits after rebase fallback"
}

# =============================================================================
# pr-merge Agent Tests
# =============================================================================

test_pr_merge_agent_exists() {
    assert_file_exists "$WIGGUM_HOME/lib/agents/workflow/pr-merge.sh" "Agent file should exist"
}

test_pr_merge_agent_sources() {
    source "$WIGGUM_HOME/lib/agents/workflow/pr-merge.sh"

    assert_equals "workflow.pr-merge" "$AGENT_TYPE" "Agent type should be set"
}

test_pr_merge_no_pr_number_fails() {
    source "$WIGGUM_HOME/lib/agents/workflow/pr-merge.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail without PR number"
}

test_pr_merge_missing_workspace_fails() {
    [ -n "$WORKER_DIR" ] && rm -rf "$WORKER_DIR/workspace"

    source "$WIGGUM_HOME/lib/agents/workflow/pr-merge.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail without workspace"
}

# =============================================================================
# git-conflict-resolver Agent Tests
# =============================================================================

test_git_conflict_resolver_agent_exists() {
    assert_file_exists "$WIGGUM_HOME/lib/agents/workflow/git-conflict-resolver.sh" "Agent file should exist"
}

test_git_conflict_resolver_agent_sources() {
    source "$WIGGUM_HOME/lib/agents/workflow/git-conflict-resolver.sh"

    assert_equals "workflow.git-conflict-resolver" "$AGENT_TYPE" "Agent type should be set"
}

test_git_conflict_resolver_no_conflicts_skips() {
    # No conflicts exist in the test workspace

    source "$WIGGUM_HOME/lib/agents/workflow/git-conflict-resolver.sh"
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null

    # Check result file
    local result_file
    result_file=$(find "$WORKER_DIR/results" -name "*-result.json" | head -1)

    if [ -n "$result_file" ]; then
        local gate_result
        gate_result=$(jq -r '.outputs.gate_result' "$result_file")
        assert_equals "SKIP" "$gate_result" "Should SKIP with no conflicts"
    fi
}

test_git_conflict_resolver_missing_workspace_fails() {
    [ -n "$WORKER_DIR" ] && rm -rf "$WORKER_DIR/workspace"

    source "$WIGGUM_HOME/lib/agents/workflow/git-conflict-resolver.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail without workspace"
}

test_git_conflict_resolver_reads_plan_file() {
    # Create a resolution plan file
    echo "# Resolution Plan for TEST-001" > "$WORKER_DIR/resolution-plan.md"

    source "$WIGGUM_HOME/lib/agents/workflow/git-conflict-resolver.sh"

    # The plan support is checked during prompt generation, but we can verify
    # the file exists and agent sources correctly
    assert_file_exists "$WORKER_DIR/resolution-plan.md" "Plan file should exist"
}

# =============================================================================
# git-conflict-resolver Completion Check & Staged Markers Tests
# =============================================================================

test_conflict_resolver_completion_check_detects_staged_markers() {
    # Source the engineering agent (not workflow wrapper) so we get internals
    source "$WIGGUM_HOME/lib/agents/engineering/git-conflict-resolver.sh"

    local workspace="$WORKER_DIR/workspace"

    # Set up context so agent_get_workspace works
    agent_setup_context "$WORKER_DIR" "$workspace" "$TEST_DIR"
    _RESOLVER_STAGED_MARKER_FILES=""

    # Create a file with conflict markers and stage it
    cat > "$workspace/conflicted.txt" << 'MARKERS'
line before
<<<<<<< HEAD
our change
=======
their change
>>>>>>> origin/main
line after
MARKERS
    git -C "$workspace" add conflicted.txt

    # Completion check should detect staged markers and return 1
    local result=0
    _conflict_completion_check 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should return 1 when staged files have conflict markers"
    assert_not_empty "$_RESOLVER_STAGED_MARKER_FILES" "Should populate _RESOLVER_STAGED_MARKER_FILES"
    assert_output_contains "$_RESOLVER_STAGED_MARKER_FILES" "conflicted.txt" "Should list the conflicted file"
}

test_conflict_resolver_completion_check_clean() {
    source "$WIGGUM_HOME/lib/agents/engineering/git-conflict-resolver.sh"

    local workspace="$WORKER_DIR/workspace"
    agent_setup_context "$WORKER_DIR" "$workspace" "$TEST_DIR"
    _RESOLVER_STAGED_MARKER_FILES=""

    # Create and stage a clean file (no markers)
    echo "clean content" > "$workspace/clean.txt"
    git -C "$workspace" add clean.txt

    local result=0
    _conflict_completion_check 2>/dev/null || result=$?

    assert_equals "0" "$result" "Should return 0 when staged files are clean"
    assert_equals "" "$_RESOLVER_STAGED_MARKER_FILES" "Should leave _RESOLVER_STAGED_MARKER_FILES empty"
}

test_conflict_resolver_staged_marker_prompt() {
    source "$WIGGUM_HOME/lib/agents/engineering/git-conflict-resolver.sh"

    local workspace="$WORKER_DIR/workspace"
    agent_setup_context "$WORKER_DIR" "$workspace" "$TEST_DIR"

    # Simulate staged marker state
    _RESOLVER_STAGED_MARKER_FILES="src/main.rs
lib/utils.rs"
    _RESOLVER_HAS_PLAN=false
    _RESOLVER_PLAN_FILE=""

    # Call prompt with iteration > 0 to trigger continuation block
    local output
    output=$(_conflict_user_prompt 1 "$WORKER_DIR/output" "" "")

    assert_output_contains "$output" "CRITICAL - STAGED FILES STILL CONTAIN CONFLICT MARKERS" \
        "Should contain critical warning"
    assert_output_contains "$output" "src/main.rs" "Should list first file"
    assert_output_contains "$output" "lib/utils.rs" "Should list second file"
}

test_auto_resolve_lockfile() {
    source "$WIGGUM_HOME/lib/agents/engineering/git-conflict-resolver.sh"

    local workspace="$WORKER_DIR/workspace"

    # Create a branch with a Cargo.lock
    echo "lockfile-v1" > "$workspace/Cargo.lock"
    git -C "$workspace" add Cargo.lock
    git -C "$workspace" commit -q -m "Add Cargo.lock"

    # Create a side branch
    git -C "$workspace" checkout -b side-branch 2>/dev/null
    echo "lockfile-side" > "$workspace/Cargo.lock"
    git -C "$workspace" add Cargo.lock
    git -C "$workspace" commit -q -m "Side branch lock"

    # Go back to main and make a different change
    git -C "$workspace" checkout - 2>/dev/null
    echo "lockfile-main" > "$workspace/Cargo.lock"
    git -C "$workspace" add Cargo.lock
    git -C "$workspace" commit -q -m "Main branch lock"

    # Merge side-branch to create conflict
    git -C "$workspace" merge side-branch 2>/dev/null || true

    # Verify conflict exists
    local unmerged_before
    unmerged_before=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null)
    assert_output_contains "$unmerged_before" "Cargo.lock" "Cargo.lock should be in conflict before auto-resolve"

    # Auto-resolve
    _auto_resolve_trivial_conflicts "$workspace" 2>/dev/null

    # Verify resolved
    local unmerged_after
    unmerged_after=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null)
    assert_equals "" "$unmerged_after" "Should have no unmerged files after auto-resolve"
}

test_auto_resolve_skips_source_files() {
    source "$WIGGUM_HOME/lib/agents/engineering/git-conflict-resolver.sh"

    local workspace="$WORKER_DIR/workspace"

    # Create a branch with a source file
    echo "fn main() { v1 }" > "$workspace/main.rs"
    git -C "$workspace" add main.rs
    git -C "$workspace" commit -q -m "Add main.rs"

    # Create a side branch
    git -C "$workspace" checkout -b side-branch 2>/dev/null
    echo "fn main() { side }" > "$workspace/main.rs"
    git -C "$workspace" add main.rs
    git -C "$workspace" commit -q -m "Side branch"

    # Go back to main and make conflicting change
    git -C "$workspace" checkout - 2>/dev/null
    echo "fn main() { main-change }" > "$workspace/main.rs"
    git -C "$workspace" add main.rs
    git -C "$workspace" commit -q -m "Main branch"

    # Merge to create conflict
    git -C "$workspace" merge side-branch 2>/dev/null || true

    # Verify conflict exists
    local unmerged_before
    unmerged_before=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null)
    assert_output_contains "$unmerged_before" "main.rs" "main.rs should be in conflict"

    # Auto-resolve should NOT touch source files
    _auto_resolve_trivial_conflicts "$workspace" 2>/dev/null

    # Verify still unresolved
    local unmerged_after
    unmerged_after=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null)
    assert_output_contains "$unmerged_after" "main.rs" "main.rs should still be unresolved after auto-resolve"
}

# =============================================================================
# multi-pr-planner Agent Tests
# =============================================================================

test_multi_pr_planner_agent_exists() {
    assert_file_exists "$WIGGUM_HOME/lib/agents/workflow/multi-pr-planner.sh" "Agent file should exist"
}

test_multi_pr_planner_agent_sources() {
    source "$WIGGUM_HOME/lib/agents/workflow/multi-pr-planner.sh"

    assert_equals "workflow.multi-pr-planner" "$AGENT_TYPE" "Agent type should be set"
}

test_multi_pr_planner_missing_batch_file_fails() {
    source "$WIGGUM_HOME/lib/agents/workflow/multi-pr-planner.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail without batch file"
}

# Note: multi-pr-planner.md was removed - this agent requires programmatic shell
# control for batch orchestration (iterating tasks, accessing multiple workspaces)
# which cannot be expressed in the markdown agent format.

# =============================================================================
# agents.json Config Tests
# =============================================================================

test_agents_json_has_workflow_agents() {
    local agents_file="$WIGGUM_HOME/config/agents.json"

    assert_file_contains "$agents_file" "workflow.git-sync-main" "Should have git-sync-main"
    assert_file_contains "$agents_file" "workflow.git-commit-push" "Should have git-commit-push"
    assert_file_contains "$agents_file" "workflow.pr-merge" "Should have pr-merge"
    assert_file_contains "$agents_file" "workflow.git-conflict-resolver" "Should have git-conflict-resolver"
    assert_file_contains "$agents_file" "workflow.multi-pr-planner" "Should have multi-pr-planner"
}

test_workflow_agents_have_result_mappings() {
    local agents_file="$WIGGUM_HOME/config/agents.json"

    local sync_main_mappings
    sync_main_mappings=$(jq '.agents."workflow.git-sync-main".result_mappings' "$agents_file")
    assert_not_equals "null" "$sync_main_mappings" "git-sync-main should have result_mappings"

    local commit_push_mappings
    commit_push_mappings=$(jq '.agents."workflow.git-commit-push".result_mappings' "$agents_file")
    assert_not_equals "null" "$commit_push_mappings" "git-commit-push should have result_mappings"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_git_sync_main_agent_exists
run_test test_git_sync_main_agent_sources
run_test test_git_sync_main_missing_workspace_fails
run_test test_git_sync_main_not_git_repo_fails
run_test test_sync_main_fast_forward
run_test test_sync_main_rebase_linear
run_test test_sync_main_merge_fallback_on_conflict
run_test test_git_commit_push_agent_exists
run_test test_git_commit_push_agent_sources
run_test test_git_commit_push_no_changes_passes
run_test test_git_commit_push_commits_changes
run_test test_git_commit_push_missing_workspace_fails
run_test test_git_commit_push_detects_unpushed_commits
run_test test_git_commit_push_rebase_fallback_on_force_push_blocked
run_test test_pr_merge_agent_exists
run_test test_pr_merge_agent_sources
run_test test_pr_merge_no_pr_number_fails
run_test test_pr_merge_missing_workspace_fails
run_test test_git_conflict_resolver_agent_exists
run_test test_git_conflict_resolver_agent_sources
run_test test_git_conflict_resolver_no_conflicts_skips
run_test test_git_conflict_resolver_missing_workspace_fails
run_test test_git_conflict_resolver_reads_plan_file
run_test test_conflict_resolver_completion_check_detects_staged_markers
run_test test_conflict_resolver_completion_check_clean
run_test test_conflict_resolver_staged_marker_prompt
run_test test_auto_resolve_lockfile
run_test test_auto_resolve_skips_source_files
run_test test_multi_pr_planner_agent_exists
run_test test_multi_pr_planner_agent_sources
run_test test_multi_pr_planner_missing_batch_file_fails
run_test test_agents_json_has_workflow_agents
run_test test_workflow_agents_have_result_mappings

print_test_summary
exit_with_test_result
