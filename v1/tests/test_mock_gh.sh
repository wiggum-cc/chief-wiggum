#!/usr/bin/env bash
# test_mock_gh.sh - Verify mock-gh.sh functionality

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$TESTS_DIR/test-framework.sh"
source "$TESTS_DIR/mocks/mock-helpers.sh"
source "$TESTS_DIR/mocks/mock-gh-helpers.sh"

setup() {
    mock_setup
    mock_gh_setup
}

teardown() {
    mock_gh_teardown
    mock_teardown
}

test_pr_lifecycle() {
    # 1. Create PR
    local result
    result=$(gh pr create --title "My PR" --body "Fixes stuff")
    assert_output_contains "$result" "https://github.com/mock/repo/pull/1"
    assert_gh_invoked_with 1 "create"
    
    # 2. List PRs
    local list_output
    list_output=$(gh pr list)
    assert_output_contains "$list_output" "My PR"
    assert_output_contains "$list_output" "OPEN"
    
    # 3. Merge PR
    local merge_output
    merge_output=$(gh pr merge 1)
    assert_output_contains "$merge_output" "Merged pull request #1"
    
    # 4. Verify state is MERGED
    local view_output
    view_output=$(gh pr list)
    assert_output_contains "$view_output" "MERGED"
}

test_issue_lifecycle() {
    local result
    result=$(gh issue create --title "Bug report" --body "It broke")
    assert_output_contains "$result" "https://github.com/mock/repo/issues/1"
    
    local list_output
    list_output=$(gh issue list)
    assert_output_contains "$list_output" "Bug report"
}

test_json_output() {
    gh issue create --title "JSON Test" --body "Body" > /dev/null
    
    local json_out
    json_out=$(gh issue list --json number,title)
    
    # Should be valid JSON array
    if echo "$json_out" | jq -e '.[0].title == "JSON Test"' > /dev/null; then
         echo -e "  ${GREEN}✓${NC} valid JSON output verified"
    else
         echo -e "  ${RED}✗${NC} invalid JSON output: $json_out"
         return 1
    fi
}

echo "=== Mock Gh Tests ==="
run_test test_pr_lifecycle
run_test test_issue_lifecycle
run_test test_json_output

print_test_summary
exit_with_test_result
