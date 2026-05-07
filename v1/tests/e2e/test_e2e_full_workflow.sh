#!/usr/bin/env bash
# test_e2e_full_workflow.sh
#
# FULL E2E WORKFLOW SCENARIO
#
# Simulates an agent workflow using the mock-git and mock-gh harnesses.
# This test acts as the "Agent" performing actions to verify the harnesses
# support the complex scenarios required (conflicts, PR lifecycle).

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$TESTS_DIR/test-framework.sh"
source "$TESTS_DIR/mocks/mock-helpers.sh"
source "$TESTS_DIR/mocks/mock-git-helpers.sh"
source "$TESTS_DIR/mocks/mock-gh-helpers.sh"

setup() {
    mock_setup
    mock_git_setup
    mock_gh_setup
    
    # Create valid git repo for the "local" workspace
    mkdir -p "$MOCK_DIR/workspace"
    cd "$MOCK_DIR/workspace"
    # We use the REAL git to initialize the repo structure that our mock will operate on
    # (since mock-git passes through by default)
    # But we need to ensure we call the REAL git, not our mock, for setup if we want to be sure.
    # However, our mock passes through, so it should be fine.
    
    # Unset mocks triggers for setup
    unset MOCK_GIT_SCENARIO
    
    git init --initial-branch=main
    git config user.email "bot@example.com"
    git config user.name "Bot"
    echo "Initial content" > file.txt
    git add file.txt
    git commit -m "Initial commit"
    
    # Setup a "remote" to push to
    mkdir -p "$MOCK_DIR/remote.git"
    git clone --bare "$MOCK_DIR/workspace" "$MOCK_DIR/remote.git"
    git remote add origin "$MOCK_DIR/remote.git"
    git fetch
}

teardown() {
    mock_gh_teardown
    mock_git_teardown
    mock_teardown
}

test_full_workflow_conflict_and_pr() {
    echo "Starting Full Workflow Simulation..."
    
    # 1. Agent starts work on a task -> New branch
    echo "Step 1: Create Branch"
    git checkout -b feature/task-123
    
    # 2. Agent modifies files
    echo "Step 2: Modify Files"
    echo " Feature content" >> file.txt
    git add file.txt
    git commit -m "feat: content"
    
    # 3. Simulate Main branch moving forward (creating potential conflict)
    # We do this "out of band" in the remote
    (
        cd "$MOCK_DIR"
        git clone "$MOCK_DIR/remote.git" "other-workspace"
        cd "other-workspace"
        echo "Conflict content" >> file.txt
        git add file.txt
        git commit -m "update: main changed"
        git push origin main
    )
    
    # 4. Agent tries to sync/merge main -> CONFLICT
    echo "Step 3: Sync and Encounter Conflict"
    # We enable the mock scenario to ENSURE failure and conflict markers are consistent
    # even if real git would do it, we want to test the harness control.
    # BUT, for this E2E, we might want to rely on REAL git logic since we set up real state?
    # The user asked for "using Git... and work within them with certain test scenarios... creating merge conflicts".
    # If we use `mock-git` scenario "merge-conflict", it forces failure regardless of state.
    # Let's use the explicit scenario to verify that functionality.
    
    export MOCK_GIT_SCENARIO="merge-conflict"
    export MOCK_GIT_CONFLICT_FILE="$MOCK_DIR/workspace/file.txt"
    
    local code=0
    git fetch origin
    git merge origin/main || code=$?
    
    assert_equals "1" "$code" "Merge should fail due to conflict scenario"
    assert_file_contains "file.txt" "<<<<<<< HEAD" "File should have conflict markers"
    
    # 5. Agent resolves conflict
    echo "Step 4: Resolve Conflict"
    unset MOCK_GIT_SCENARIO
    
    # Manually fix file
    echo "Resolved Content" > file.txt
    git add file.txt
    git commit -m "merge: resolved conflict"
    
    # 6. Push to remote
    echo "Step 5: Push Branch"
    git push -u origin feature/task-123
    
    # 7. Create PR via GH
    echo "Step 6: Create PR"
    local pr_url
    pr_url=$(gh pr create --title "Feature Task 123" --body "Implements things")
    assert_output_contains "$pr_url" "https://github.com/mock/repo/pull/1"
    
    # 8. Verify PR exists
    echo "Step 7: Verify PR"
    local pr_list
    pr_list=$(gh pr list)
    assert_output_contains "$pr_list" "Feature Task 123"
    
    # 9. Merge PR via GH
    echo "Step 8: Merge PR"
    gh pr merge 1
    
    # 10. Verify Merged
    echo "Step 9: Verify Merged Status"
    local final_status
    final_status=$(gh pr view 1 --json state | jq -r .state)
    assert_equals "MERGED" "$final_status"
    
    echo "Full Workflow Completed Successfully"
}

run_test test_full_workflow_conflict_and_pr

print_test_summary
exit_with_test_result
