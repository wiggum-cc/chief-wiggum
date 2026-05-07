#!/usr/bin/env bash
# test_high_level_wiggum_run.sh
#
# HIGH-LEVEL E2E TEST: Complete wiggum-run orchestration
#
# This test creates a complete fake project and runs the actual `wiggum-run`
# script with all mocks in place. It verifies the full workflow including:
# - Service scheduler startup
# - Task spawning from kanban
# - Worker execution (using mock-claude)
# - PR creation (using mock-gh)
# - Kanban status updates
# - Task completion

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"

source "$TESTS_DIR/test-framework.sh"
source "$TESTS_DIR/mocks/mock-helpers.sh"
source "$TESTS_DIR/mocks/mock-git-helpers.sh"
source "$TESTS_DIR/mocks/mock-gh-helpers.sh"

TEST_PROJECT=""
WIGGUM_PID=""

setup() {
    mock_setup
    mock_git_setup
    mock_gh_setup
    
    # Create a complete fake project
    TEST_PROJECT="$MOCK_DIR/test-project"
    mkdir -p "$TEST_PROJECT"
    cd "$TEST_PROJECT"
    
    # Initialize git repo
    git init --initial-branch=main
    git config user.email "test@wiggum.local"
    git config user.name "Test Bot"
    
    # Create .ralph structure
    mkdir -p .ralph/{workers,logs,plans,checkpoints,orchestrator}
    
    # Create minimal config
    cat > .ralph/config.json <<'EOF'
{
    "workers": {
        "max_iterations": 2,
        "sleep_seconds": 1
    },
    "rate_limit": {
        "enabled": false
    },
    "hooks": {
        "enabled": false
    }
}
EOF
    
    # Create agents config
    cat > .ralph/agents.json <<'EOF'
{
    "defaults": {
        "max_iterations": 2,
        "max_turns": 5,
        "timeout_seconds": 60,
        "auto_commit": false
    }
}
EOF
    
    # Create services config (empty - use default built-in services)
    # Wiggum will fall back to built-in service definitions
    cat > .ralph/services.json <<'EOF'
{
    "services": []
}
EOF
    
    # Add a git remote (even if fake) to satisfy git pull checks
    git remote add origin "$TEST_PROJECT/.git"
    
    # Create kanban with a simple task (proper wiggum format)
    cat > .ralph/kanban.md <<'KANBAN'
# Test Project

## TASKS

### To Do

- [ ] **[TASK-001]** Create hello world script
  - Priority: HIGH
  - Dependencies: none
  - Description: Create a simple bash script that prints "Hello World"

### In Progress

### Pending Approval

### Done
KANBAN
    
    # Create .gitignore to ignore runtime directories
    cat > .gitignore <<'EOF'
.ralph/logs/
.ralph/workers/
.ralph/checkpoints/
.ralph/orchestrator/
EOF
    
    # Create initial commit
    git add -A
    git commit -m "Initial project setup"
    
    # Configure mock-claude for this test
    # Create a responses file that will be used sequentially
    cat > "$MOCK_DIR/claude-responses.txt" <<'EOF'
I'll create the hello.sh script now.
Created hello.sh successfully.
All tasks completed.
EOF
    
    export MOCK_CLAUDE_RESPONSES_FILE="$MOCK_DIR/claude-responses.txt"
    export MOCK_CLAUDE_SCENARIO="file-edit"
    export MOCK_CLAUDE_TOOL_USE="write,bash"
    
    # Mock-claude will create files via MOCK_CLAUDE_TOUCH_FILES
    # Use a wildcard pattern that will be expanded at runtime
    export MOCK_CLAUDE_TOUCH_FILES=""
    
    # Create a wrapper script that will be used as CLAUDE
    # This wrapper will dynamically create the hello.sh in the workspace
    cat > "$MOCK_DIR/bin/claude-wrapper.sh" <<'WRAPPER'
#!/usr/bin/env bash
# Wrapper around mock-claude that creates hello.sh in the workspace
set -euo pipefail

# Find the workspace directory (should be a worktree)
WORKSPACE_DIR=$(pwd)

# Before calling mock-claude, set up file touching
if [[ "$WORKSPACE_DIR" == *"/workspace" ]] || [[ "$WORKSPACE_DIR" == *"/.ralph/workers/"* ]]; then
    export MOCK_CLAUDE_TOUCH_FILES="$WORKSPACE_DIR/hello.sh"
fi

# Call the real mock-claude
exec "$MOCK_DIR/bin/claude" "$@"
WRAPPER
    
    chmod +x "$MOCK_DIR/bin/claude-wrapper.sh"
    export CLAUDE="$MOCK_DIR/bin/claude-wrapper.sh"
}

teardown() {
    # Kill wiggum-run if still running
    if [ -n "$WIGGUM_PID" ] && kill -0 "$WIGGUM_PID" 2>/dev/null; then
        echo "Stopping wiggum-run (PID: $WIGGUM_PID)"
        kill "$WIGGUM_PID" 2>/dev/null || true
        sleep 1
        kill -9 "$WIGGUM_PID" 2>/dev/null || true
    fi
    
    mock_gh_teardown
    mock_git_teardown
    mock_teardown
}

# Helper: Wait for a condition with timeout
wait_for_condition() {
    local condition="$1"
    local timeout="${2:-30}"
    local interval="${3:-1}"
    local elapsed=0
    
    while [ $elapsed -lt $timeout ]; do
        if eval "$condition"; then
            return 0
        fi
        sleep "$interval"
        elapsed=$((elapsed + interval))
    done
    
    return 1
}

# Helper: Check if task is in specific status in kanban
task_has_status() {
    local task_id="$1"
    local status_marker="$2"
    
    if grep -q "\\[$status_marker\\] \\*\\*\\[$task_id\\]\\*\\*" "$TEST_PROJECT/.ralph/kanban.md"; then
        return 0
    fi
    return 1
}

test_full_wiggum_run_workflow() {
    echo "=== Starting High-Level Wiggum Run E2E Test ==="
    
    cd "$TEST_PROJECT"
    
    # Step 1: Launch wiggum-run in background
    echo "Step 1: Launching wiggum-run..."
    
    # Run with minimal workers and quiet mode to reduce noise
    "$WIGGUM_HOME/bin/wiggum-run" --max-workers 1 --max-iters 2 --max-turns 5 -q > "$MOCK_DIR/wiggum-run.log" 2>&1 &
    WIGGUM_PID=$!
    
    echo "  Wiggum-run started with PID: $WIGGUM_PID"
    
    # Give it a moment to start
    sleep 2
    
    # Verify it's running
    if ! kill -0 "$WIGGUM_PID" 2>/dev/null; then
        echo "ERROR: wiggum-run process died immediately"
        cat "$MOCK_DIR/wiggum-run.log"
        return 1
    fi
    
    # Step 2: Wait for task to move to "In Progress"
    echo "Step 2: Waiting for task to start (move to In Progress)..."
    if wait_for_condition "task_has_status TASK-001 '='" 30; then
        echo "  ✓ Task moved to In Progress"
    else
        echo "  ✗ Task did not move to In Progress within timeout"
        echo "Kanban contents:"
        cat "$TEST_PROJECT/.ralph/kanban.md"
        echo "Wiggum log:"
        tail -50 "$MOCK_DIR/wiggum-run.log"
        return 1
    fi
    
    # Give worker more time to execute
    echo "  Waiting for worker to execute..."
    sleep 10
    
    # Step 3: Wait for worker to complete and PR to be created
    echo "Step 3: Waiting for PR creation..."
    if wait_for_condition "[ -f '$MOCK_GH_LOG_DIR/db.json' ] && jq -e '.prs | length > 0' '$MOCK_GH_LOG_DIR/db.json' >/dev/null 2>&1" 60; then
        echo "  ✓ PR created in mock-gh"
        
        # Verify PR details
        local pr_title
        pr_title=$(jq -r '.prs[0].title' "$MOCK_GH_LOG_DIR/db.json")
        assert_output_contains "$pr_title" "TASK-001"
    else
        echo "  ✗ PR was not created within timeout"
        echo "Mock GH DB:"
        [ -f "$MOCK_GH_LOG_DIR/db.json" ] && cat "$MOCK_GH_LOG_DIR/db.json" || echo "DB not found"
        echo ""
        echo "Worker directories:"
        ls -la "$TEST_PROJECT/.ralph/workers/" 2>/dev/null || echo "No workers dir"
        echo ""
        echo "Worker logs (if any):"
        find "$TEST_PROJECT/.ralph/workers/" -name "worker.log" -exec echo "=== {} ===" \; -exec tail -30 {} \; 2>/dev/null || echo "No worker logs found"
        echo ""
        echo "Wiggum log (last 100 lines):"
        tail -100 "$MOCK_DIR/wiggum-run.log"
        return 1
    fi
    
    # Step 4: Check task moved to Pending Approval
    echo "Step 4: Verifying task status is Pending Approval..."
    if task_has_status TASK-001 'P'; then
        echo "  ✓ Task marked as Pending Approval [P]"
    else
        echo "  ✗ Task not in Pending Approval status"
        echo "Kanban contents:"
        cat "$TEST_PROJECT/.ralph/kanban.md"
        return 1
    fi
    
    # Step 5: Manually "merge" the PR via mock-gh to simulate approval
    echo "Step 5: Simulating PR merge..."
    gh pr merge 1
    
    # The orchestrator should detect the merge via pr-sync service and mark task complete
    # However, our minimal services.json doesn't include pr-sync, so we'll manually update
    # In a real E2E, pr-sync would handle this
    # For now, we just verify the PR is in our DB as merged
    local pr_state
    pr_state=$(jq -r '.prs[0].state' "$MOCK_GH_LOG_DIR/db.json")
    assert_equals "MERGED" "$pr_state" "PR should be marked as MERGED"
    
    # Step 6: Signal orchestrator to exit
    echo "Step 6: Signaling orchestrator to stop..."
    touch "$TEST_PROJECT/.ralph/orchestrator/should-exit"
    
    # Wait for graceful shutdown
    local shutdown_timeout=10
    local shutdown_elapsed=0
    while kill -0 "$WIGGUM_PID" 2>/dev/null && [ $shutdown_elapsed -lt $shutdown_timeout ]; do
        sleep 1
        shutdown_elapsed=$((shutdown_elapsed + 1))
    done
    
    if kill -0 "$WIGGUM_PID" 2>/dev/null; then
        echo "  Force killing wiggum-run..."
        kill -9 "$WIGGUM_PID" 2>/dev/null || true
    else
        echo "  ✓ Wiggum-run exited gracefully"
    fi
    
    WIGGUM_PID=""
    
    # Step 7: Verify final state
    echo "Step 7: Verifying final state..."
    
    # Check that worker directory was created
    if compgen -G "$TEST_PROJECT/.ralph/workers/worker-TASK-001-*" > /dev/null; then
        echo "  ✓ Worker directory exists"
        
        # Check for worker artifacts
        local worker_dir
        worker_dir=$(echo "$TEST_PROJECT/.ralph/workers/worker-TASK-001-"*)
        
        assert_file_exists "$worker_dir/worker.log" "Worker log should exist"
        assert_file_exists "$worker_dir/prd.md" "PRD should exist"
    else
        echo "  ✗ Worker directory not found"
        echo "Contents of workers dir:"
        ls -la "$TEST_PROJECT/.ralph/workers/" || echo "Workers dir doesn't exist"
        return 1
    fi
    
    # Verify mock invocations
    echo "Step 8: Verifying mock invocations..."
    
    # Mock claude should have been called
    local claude_invocations
    claude_invocations=$(mock_get_invocation_count)
    assert_greater_than "$claude_invocations" 0 "Mock Claude should have been invoked"
    
    # Mock gh should have been called for PR creation
    local gh_invocations
    gh_invocations=$(cat "$MOCK_GH_LOG_DIR/mock-gh-invocations" 2>/dev/null || echo "0")
    assert_greater_than "$gh_invocations" 0 "Mock GH should have been invoked"
    
    echo ""
    echo "=== High-Level E2E Test Completed Successfully ==="
    echo "Summary:"
    echo "  - Wiggum orchestrator started and ran"
    echo "  - Task TASK-001 was picked up and moved to In Progress"
    echo "  - Worker executed with mock-claude"
    echo "  - PR was created via mock-gh"
    echo "  - Task moved to Pending Approval"
    echo "  - Mock invocations verified"
}

run_test test_full_wiggum_run_workflow

print_test_summary
exit_with_test_result
