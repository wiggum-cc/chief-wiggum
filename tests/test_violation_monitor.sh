#!/usr/bin/env bash
# Test violation-monitor.sh destructive git command detection

set -e

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

# Source the violation monitor
source "$WIGGUM_HOME/lib/worker/violation-monitor.sh"

echo "Testing violation-monitor.sh destructive git command detection..."
echo ""

# Track test results
PASSED=0
FAILED=0

# Test helper: expect command to be detected as destructive (returns 0)
expect_destructive() {
    local cmd="$1"
    local desc="$2"
    if _is_destructive_git_command "$cmd"; then
        echo "  [PASS] $desc"
        PASSED=$((PASSED + 1))
    else
        echo "  [FAIL] $desc (expected destructive, got safe)"
        FAILED=$((FAILED + 1))
    fi
}

# Test helper: expect command to be detected as safe (returns 1)
expect_safe() {
    local cmd="$1"
    local desc="$2"
    if _is_destructive_git_command "$cmd"; then
        echo "  [FAIL] $desc (expected safe, got destructive)"
        FAILED=$((FAILED + 1))
    else
        echo "  [PASS] $desc"
        PASSED=$((PASSED + 1))
    fi
}

echo "=== Testing DESTRUCTIVE commands (should be blocked) ==="
echo ""

echo "-- git checkout -- (file revert) --"
expect_destructive "git checkout -- file.txt" "git checkout -- file.txt"
expect_destructive "git checkout -- ." "git checkout -- ."
expect_destructive "git checkout -- src/main.rs" "git checkout -- src/main.rs"
expect_destructive "git checkout HEAD -- file.txt" "git checkout HEAD -- file.txt"

echo ""
echo "-- git checkout . (revert all) --"
expect_destructive "git checkout ." "git checkout ."

echo ""
echo "-- git stash --"
expect_destructive "git stash" "git stash"
expect_destructive "git stash push" "git stash push"
expect_destructive "git stash save 'message'" "git stash save 'message'"
expect_destructive "git stash pop" "git stash pop"
expect_destructive "git stash drop" "git stash drop"

echo ""
echo "-- git reset --hard --"
expect_destructive "git reset --hard" "git reset --hard"
expect_destructive "git reset --hard HEAD" "git reset --hard HEAD"
expect_destructive "git reset --hard HEAD~1" "git reset --hard HEAD~1"
expect_destructive "git reset --hard origin/main" "git reset --hard origin/main"

echo ""
echo "-- git reset (commit manipulation) --"
expect_destructive "git reset HEAD~1" "git reset HEAD~1"
expect_destructive "git reset HEAD~" "git reset HEAD~"
expect_destructive "git reset abc123" "git reset abc123"

echo ""
echo "-- git clean --"
expect_destructive "git clean" "git clean"
expect_destructive "git clean -f" "git clean -f"
expect_destructive "git clean -fd" "git clean -fd"
expect_destructive "git clean -fdx" "git clean -fdx"

echo ""
echo "-- git restore --"
expect_destructive "git restore file.txt" "git restore file.txt"
expect_destructive "git restore --staged file.txt" "git restore --staged file.txt"
expect_destructive "git restore ." "git restore ."

echo ""
echo "-- git revert --"
expect_destructive "git revert HEAD" "git revert HEAD"
expect_destructive "git revert abc123" "git revert abc123"

echo ""
echo "=== Testing SAFE commands (should be allowed) ==="
echo ""

echo "-- Read-only commands --"
expect_safe "git status" "git status"
expect_safe "git diff" "git diff"
expect_safe "git diff --staged" "git diff --staged"
expect_safe "git log" "git log"
expect_safe "git log --oneline -10" "git log --oneline -10"
expect_safe "git show HEAD" "git show HEAD"
expect_safe "git show abc123" "git show abc123"
expect_safe "git branch" "git branch"
expect_safe "git branch -a" "git branch -a"
expect_safe "git remote -v" "git remote -v"
expect_safe "git rev-parse HEAD" "git rev-parse HEAD"
expect_safe "git ls-files" "git ls-files"
expect_safe "git describe --tags" "git describe --tags"

echo ""
echo "-- git add (staging) --"
expect_safe "git add file.txt" "git add file.txt"
expect_safe "git add ." "git add ."
expect_safe "git add -A" "git add -A"
expect_safe "git add src/" "git add src/"

echo ""
echo "-- git commit --"
expect_safe "git commit -m 'message'" "git commit -m 'message'"
expect_safe "git commit -am 'message'" "git commit -am 'message'"
expect_safe "git commit --amend" "git commit --amend"

echo ""
echo "-- git checkout <branch> (branch switching) --"
expect_safe "git checkout main" "git checkout main"
expect_safe "git checkout feature-branch" "git checkout feature-branch"
expect_safe "git checkout origin/main" "git checkout origin/main"

echo ""
echo "-- Non-git commands --"
expect_safe "echo hello" "echo hello"
expect_safe "ls -la" "ls -la"
expect_safe "cat file.txt" "cat file.txt"
expect_safe "npm test" "npm test"

echo ""
echo "=== Test Results ==="
echo "Passed: $PASSED"
echo "Failed: $FAILED"
echo ""

if [ "$FAILED" -gt 0 ]; then
    echo "TESTS FAILED"
    exit 1
else
    echo "All tests passed!"
    exit 0
fi
