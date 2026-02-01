#!/usr/bin/env bash
# Tests for hooks/callbacks/validate-workspace-path.sh
set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

HOOK_SCRIPT="$WIGGUM_HOME/hooks/callbacks/validate-workspace-path.sh"

# Test environment
TEST_DIR=""
RALPH_DIR=""
WORKER_DIR=""
WORKSPACE=""

setup() {
    TEST_DIR=$(mktemp -d)
    # Create simulated directory structure:
    # TEST_DIR/
    #   .ralph/
    #     plans/
    #     results/
    #     workers/
    #       worker-TEST-001/
    #         workspace/
    #         reports/
    #         checkpoints/
    #         logs/
    RALPH_DIR="$TEST_DIR/.ralph"
    mkdir -p "$RALPH_DIR/plans"
    mkdir -p "$RALPH_DIR/results"
    WORKER_DIR="$RALPH_DIR/workers/worker-TEST-001"
    mkdir -p "$WORKER_DIR/workspace/src"
    mkdir -p "$WORKER_DIR/reports"
    mkdir -p "$WORKER_DIR/checkpoints"
    mkdir -p "$WORKER_DIR/logs"
    mkdir -p "$WORKER_DIR/summaries"
    touch "$WORKER_DIR/prd.md"
    touch "$WORKER_DIR/task-comments.md"
    touch "$WORKER_DIR/agent.pid"
    touch "$WORKER_DIR/worker.log"
    WORKSPACE="$WORKER_DIR/workspace"
}

teardown() {
    rm -rf "$TEST_DIR"
}

# Helper to run hook with JSON input
# Returns exit code (0=allow, 2=block)
run_hook() {
    local json="$1"
    local exit_code=0
    echo "$json" | WORKER_WORKSPACE="$WORKSPACE" WORKER_DIR="$WORKER_DIR" bash "$HOOK_SCRIPT" 2>/dev/null || exit_code=$?
    return $exit_code
}

# Helper to run hook and capture stderr
run_hook_with_stderr() {
    local json="$1"
    local exit_code=0
    echo "$json" | WORKER_WORKSPACE="$WORKSPACE" WORKER_DIR="$WORKER_DIR" bash "$HOOK_SCRIPT" 2>&1 || exit_code=$?
    return $exit_code
}

# =============================================================================
# Test: Workspace paths (should be allowed)
# =============================================================================

test_workspace_file_allowed() {
    local json='{"tool":"Read","tool_input":{"file_path":"'"$WORKSPACE"'/src/main.ts"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Workspace file read allowed"
    else
        echo -e "  ${RED}✗${NC} Workspace file read should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_workspace_edit_allowed() {
    local json='{"tool":"Edit","tool_input":{"file_path":"'"$WORKSPACE"'/src/main.ts"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Workspace file edit allowed"
    else
        echo -e "  ${RED}✗${NC} Workspace file edit should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_workspace_write_allowed() {
    local json='{"tool":"Write","tool_input":{"file_path":"'"$WORKSPACE"'/new-file.ts"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Workspace file write allowed"
    else
        echo -e "  ${RED}✗${NC} Workspace file write should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_workspace_glob_allowed() {
    local json='{"tool":"Glob","tool_input":{"path":"'"$WORKSPACE"'/src"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Workspace glob search allowed"
    else
        echo -e "  ${RED}✗${NC} Workspace glob search should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Test: Worker dir paths (should be allowed except blocked ones)
# =============================================================================

test_worker_reports_allowed() {
    local json='{"tool":"Read","tool_input":{"file_path":"'"$WORKER_DIR"'/reports/status.md"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Worker reports read allowed"
    else
        echo -e "  ${RED}✗${NC} Worker reports read should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_worker_prd_allowed() {
    local json='{"tool":"Read","tool_input":{"file_path":"'"$WORKER_DIR"'/prd.md"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Worker prd.md read allowed"
    else
        echo -e "  ${RED}✗${NC} Worker prd.md read should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_worker_task_comments_allowed() {
    local json='{"tool":"Read","tool_input":{"file_path":"'"$WORKER_DIR"'/task-comments.md"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Worker task-comments.md read allowed"
    else
        echo -e "  ${RED}✗${NC} Worker task-comments.md read should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_worker_summaries_allowed() {
    local json='{"tool":"Read","tool_input":{"file_path":"'"$WORKER_DIR"'/summaries/run-1/summary.txt"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Worker summaries read allowed"
    else
        echo -e "  ${RED}✗${NC} Worker summaries read should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Test: Blocked worker dir paths
# =============================================================================

test_worker_checkpoints_read_allowed() {
    local json='{"tool":"Read","tool_input":{"file_path":"'"$WORKER_DIR"'/checkpoints/checkpoint.json"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Worker checkpoints read allowed"
    else
        echo -e "  ${RED}✗${NC} Worker checkpoints read should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_worker_checkpoints_write_blocked() {
    local json='{"tool":"Write","tool_input":{"file_path":"'"$WORKER_DIR"'/checkpoints/checkpoint.json"}}'

    if run_hook "$json"; then
        echo -e "  ${RED}✗${NC} Worker checkpoints write should be blocked" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Worker checkpoints write blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_worker_logs_read_allowed() {
    local json='{"tool":"Read","tool_input":{"file_path":"'"$WORKER_DIR"'/logs/iteration-0.log"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Worker logs read allowed"
    else
        echo -e "  ${RED}✗${NC} Worker logs read should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_worker_logs_edit_blocked() {
    local json='{"tool":"Edit","tool_input":{"file_path":"'"$WORKER_DIR"'/logs/iteration-0.log"}}'

    if run_hook "$json"; then
        echo -e "  ${RED}✗${NC} Worker logs edit should be blocked" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Worker logs edit blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_worker_agent_pid_blocked() {
    local json='{"tool":"Read","tool_input":{"file_path":"'"$WORKER_DIR"'/agent.pid"}}'

    if run_hook "$json"; then
        echo -e "  ${RED}✗${NC} Worker agent.pid should be blocked" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Worker agent.pid blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_worker_log_read_allowed() {
    local json='{"tool":"Read","tool_input":{"file_path":"'"$WORKER_DIR"'/worker.log"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Worker worker.log read allowed"
    else
        echo -e "  ${RED}✗${NC} Worker worker.log read should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_worker_log_write_blocked() {
    local json='{"tool":"Write","tool_input":{"file_path":"'"$WORKER_DIR"'/worker.log"}}'

    if run_hook "$json"; then
        echo -e "  ${RED}✗${NC} Worker worker.log write should be blocked" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Worker worker.log write blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Test: Ralph dir paths (plans and results allowed)
# =============================================================================

test_ralph_plans_allowed() {
    local json='{"tool":"Read","tool_input":{"file_path":"'"$RALPH_DIR"'/plans/TASK-001.md"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Ralph plans read allowed"
    else
        echo -e "  ${RED}✗${NC} Ralph plans read should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_ralph_results_allowed() {
    local json='{"tool":"Read","tool_input":{"file_path":"'"$RALPH_DIR"'/results/TASK-001.json"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Ralph results read allowed"
    else
        echo -e "  ${RED}✗${NC} Ralph results read should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Test: Paths outside boundaries (should be blocked)
# =============================================================================

test_outside_boundary_blocked() {
    local json='{"tool":"Read","tool_input":{"file_path":"/etc/passwd"}}'

    if run_hook "$json"; then
        echo -e "  ${RED}✗${NC} Path outside boundaries should be blocked" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Path outside boundaries blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_other_worker_blocked() {
    local other_worker="$RALPH_DIR/workers/worker-OTHER-999"
    mkdir -p "$other_worker/workspace"
    local json='{"tool":"Read","tool_input":{"file_path":"'"$other_worker"'/workspace/file.ts"}}'

    if run_hook "$json"; then
        echo -e "  ${RED}✗${NC} Other worker access should be blocked" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Other worker access blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_home_dir_blocked() {
    local json='{"tool":"Read","tool_input":{"file_path":"'"$HOME"'/.bashrc"}}'

    if run_hook "$json"; then
        echo -e "  ${RED}✗${NC} Home directory access should be blocked" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Home directory access blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Test: Bash command validation
# =============================================================================

test_git_command_blocked() {
    local json='{"tool":"Bash","tool_input":{"command":"git status"}}'

    if run_hook "$json"; then
        echo -e "  ${RED}✗${NC} Git commands should be blocked" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Git commands blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_git_in_pipeline_blocked() {
    local json='{"tool":"Bash","tool_input":{"command":"echo foo | git status"}}'

    if run_hook "$json"; then
        echo -e "  ${RED}✗${NC} Git in pipeline should be blocked" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Git in pipeline blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_cd_outside_workspace_blocked() {
    local json='{"tool":"Bash","tool_input":{"command":"cd /tmp && ls"}}'

    if run_hook "$json"; then
        echo -e "  ${RED}✗${NC} cd outside workspace should be blocked" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} cd outside workspace blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_cd_inside_workspace_allowed() {
    local json='{"tool":"Bash","tool_input":{"command":"cd '"$WORKSPACE"'/src && ls"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} cd inside workspace allowed"
    else
        echo -e "  ${RED}✗${NC} cd inside workspace should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_bash_absolute_path_blocked() {
    local json='{"tool":"Bash","tool_input":{"command":"cat /home/user/secrets.txt"}}'

    if run_hook "$json"; then
        echo -e "  ${RED}✗${NC} Bash absolute path outside should be blocked" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Bash absolute path outside blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_bash_system_path_allowed() {
    local json='{"tool":"Bash","tool_input":{"command":"ls /usr/bin"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Bash system path allowed"
    else
        echo -e "  ${RED}✗${NC} Bash system path should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_bash_relative_path_to_worker_allowed() {
    local json='{"tool":"Bash","tool_input":{"command":"cat ../reports/status.md"}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Bash relative path to worker dir allowed"
    else
        echo -e "  ${RED}✗${NC} Bash relative path to worker dir should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_bash_relative_path_escape_blocked() {
    # Try to escape to project root (4 levels up from workspace)
    local json='{"tool":"Bash","tool_input":{"command":"cat ../../../../secrets.txt"}}'

    if run_hook "$json"; then
        echo -e "  ${RED}✗${NC} Bash path traversal escape should be blocked" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Bash path traversal escape blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Test: No input scenarios
# =============================================================================

test_empty_tool_input_allowed() {
    local json='{"tool":"TodoWrite","tool_input":{}}'

    if run_hook "$json"; then
        echo -e "  ${GREEN}✓${NC} Empty tool input allowed"
    else
        echo -e "  ${RED}✗${NC} Empty tool input should be allowed" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Test: Error messages are informative
# =============================================================================

test_block_error_shows_path() {
    local json='{"tool":"Write","tool_input":{"file_path":"'"$WORKER_DIR"'/checkpoints/foo"}}'
    local output
    output=$(run_hook_with_stderr "$json") || true

    if echo "$output" | grep -q "PATH ACCESS BLOCKED"; then
        echo -e "  ${GREEN}✓${NC} Block error shows PATH ACCESS BLOCKED"
    else
        echo -e "  ${RED}✗${NC} Block error should show PATH ACCESS BLOCKED" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_git_block_shows_message() {
    local json='{"tool":"Bash","tool_input":{"command":"git commit"}}'
    local output
    output=$(run_hook_with_stderr "$json") || true

    if echo "$output" | grep -q "GIT COMMAND BLOCKED"; then
        echo -e "  ${GREEN}✓${NC} Git block shows GIT COMMAND BLOCKED"
    else
        echo -e "  ${RED}✗${NC} Git block should show GIT COMMAND BLOCKED" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Run all tests
# =============================================================================

echo "Testing validate-workspace-path.sh hook"
echo ""

# Workspace tests
run_test test_workspace_file_allowed
run_test test_workspace_edit_allowed
run_test test_workspace_write_allowed
run_test test_workspace_glob_allowed

# Worker dir allowed tests
run_test test_worker_reports_allowed
run_test test_worker_prd_allowed
run_test test_worker_task_comments_allowed
run_test test_worker_summaries_allowed

# Worker dir read-only tests (read allowed, write blocked)
run_test test_worker_checkpoints_read_allowed
run_test test_worker_checkpoints_write_blocked
run_test test_worker_logs_read_allowed
run_test test_worker_logs_edit_blocked
run_test test_worker_agent_pid_blocked
run_test test_worker_log_read_allowed
run_test test_worker_log_write_blocked

# Ralph dir tests
run_test test_ralph_plans_allowed
run_test test_ralph_results_allowed

# Outside boundary tests
run_test test_outside_boundary_blocked
run_test test_other_worker_blocked
run_test test_home_dir_blocked

# Bash command tests
run_test test_git_command_blocked
run_test test_git_in_pipeline_blocked
run_test test_cd_outside_workspace_blocked
run_test test_cd_inside_workspace_allowed
run_test test_bash_absolute_path_blocked
run_test test_bash_system_path_allowed
run_test test_bash_relative_path_to_worker_allowed
run_test test_bash_relative_path_escape_blocked

# Edge case tests
run_test test_empty_tool_input_allowed

# Error message tests
run_test test_block_error_shows_path
run_test test_git_block_shows_message

print_test_summary
exit_with_test_result
