#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/distributed/heartbeat.sh — sync-state fallback

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

# Stub heavy dependencies before sourcing heartbeat.sh
# These prevent real GitHub API calls and PID checks.

# --- logger stubs (must exist before any source) ---
[ -z "${_LOGGER_LOADED:-}" ] && {
    _LOGGER_LOADED=1
    log()          { :; }
    log_debug()    { :; }
    log_info()     { :; }
    log_warn()     { echo "WARN: $*" >&2; }
    log_error()    { echo "ERROR: $*" >&2; }
}

# --- platform stubs ---
[ -z "${_PLATFORM_LOADED:-}" ] && {
    _PLATFORM_LOADED=1
    epoch_now() { date +%s; }
    iso_now()   { date -u +"%Y-%m-%dT%H:%M:%SZ"; }
}

# --- server-identity stub ---
[ -z "${_SERVER_IDENTITY_LOADED:-}" ] && {
    _SERVER_IDENTITY_LOADED=1
}

# --- claim-manager stub ---
[ -z "${_CLAIM_MANAGER_LOADED:-}" ] && {
    _CLAIM_MANAGER_LOADED=1
    claim_list_owned() { echo ""; }
}

# --- worker-lifecycle stub ---
[ -z "${_WORKER_LIFECYCLE_LOADED:-}" ] && {
    _WORKER_LIFECYCLE_LOADED=1
    is_worker_running() { return 0; }  # default: worker is running
}

# --- issue-state: source real implementation (it's lightweight) ---
source "$WIGGUM_HOME/lib/github/issue-state.sh"

# Now source heartbeat (picks up stubs, skips real deps)
source "$WIGGUM_HOME/lib/distributed/heartbeat.sh"

# =============================================================================
# Test helpers
# =============================================================================

TEST_DIR=""
RALPH_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    mkdir -p "$RALPH_DIR/workers"

    # Reset heartbeat state
    _HEARTBEAT_LAST=()
    # Set interval to 0 so throttle never blocks
    _HEARTBEAT_INTERVAL=0

    # Empty the issue cache — simulates fresh subprocess with failed API call
    declare -gA _GH_ISSUE_CACHE=()
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# heartbeat_update_all — sync-state fallback tests
# =============================================================================

test_sync_state_fallback_resolves_task_id() {
    # Setup: issue 42 maps to SPEC-009 in sync state
    local sync_state='{"version":"2.0","last_down_sync_at":0,"last_up_sync_at":0,"issues":{"SPEC-009":{"issue_number":42,"last_synced_status":" ","last_remote_state":"open","description_hash":"sha256:abc"}}}'
    echo "$sync_state" > "$RALPH_DIR/github-sync-state.json"

    # Create a worker dir that matches SPEC-009 (not GH-42)
    local worker_dir="$RALPH_DIR/workers/worker-SPEC-009-1234567890"
    mkdir -p "$worker_dir"

    # Create a PID file so is_worker_running succeeds
    echo "$$" > "$worker_dir/agent.pid"

    # Stub claim_list_owned to return issue 42
    claim_list_owned() { echo "42"; }

    # Track what heartbeat_update_task receives
    local captured_task_id=""
    heartbeat_update_task() {
        captured_task_id="$4"
        return 0
    }

    # Run heartbeat_update_all with empty _GH_ISSUE_CACHE
    heartbeat_update_all "$RALPH_DIR" "test-server"

    assert_equals "SPEC-009" "$captured_task_id" \
        "Should resolve task_id via sync-state when cache is empty"
}

test_sync_state_fallback_skips_when_no_sync_file() {
    # No github-sync-state.json exists
    # Worker dir only matches GH-42 pattern (shouldn't exist)
    local worker_dir="$RALPH_DIR/workers/worker-GH-42-1234567890"
    mkdir -p "$worker_dir"
    echo "$$" > "$worker_dir/agent.pid"

    claim_list_owned() { echo "42"; }

    local captured_task_id=""
    heartbeat_update_task() {
        captured_task_id="$4"
        return 0
    }

    heartbeat_update_all "$RALPH_DIR" "test-server"

    assert_equals "GH-42" "$captured_task_id" \
        "Should fall back to GH-<number> when no sync state file"
}

test_sync_state_fallback_keeps_cache_result_when_available() {
    # Setup: populate the issue cache with real data
    declare -gA _GH_ISSUE_CACHE=([42]="**[SPEC-009]** Some task title")

    # Stub _github_parse_task_id to extract from title
    _github_parse_task_id() {
        echo "$1" | grep -oP '\[([A-Za-z]+-[0-9]+)\]' | tr -d '[]' | head -1
    }

    # Create sync state with a DIFFERENT task ID to verify cache wins
    local sync_state='{"version":"2.0","last_down_sync_at":0,"last_up_sync_at":0,"issues":{"WRONG-001":{"issue_number":42,"last_synced_status":" ","last_remote_state":"open","description_hash":"sha256:abc"}}}'
    echo "$sync_state" > "$RALPH_DIR/github-sync-state.json"

    local worker_dir="$RALPH_DIR/workers/worker-SPEC-009-1234567890"
    mkdir -p "$worker_dir"
    echo "$$" > "$worker_dir/agent.pid"

    claim_list_owned() { echo "42"; }

    local captured_task_id=""
    heartbeat_update_task() {
        captured_task_id="$4"
        return 0
    }

    heartbeat_update_all "$RALPH_DIR" "test-server"

    assert_equals "SPEC-009" "$captured_task_id" \
        "Should use cache result when available (not sync-state fallback)"
}

test_cache_refresh_failure_logs_warning() {
    # Stub _github_refresh_cache to fail
    _github_refresh_cache() { return 1; }

    claim_list_owned() { echo ""; }

    local warn_output
    warn_output=$(heartbeat_update_all "$RALPH_DIR" "test-server" 2>&1)

    assert_output_contains "$warn_output" "issue cache refresh failed" \
        "Should log warning when cache refresh fails"
}

test_shutdown_sync_state_fallback() {
    # Setup: issue 99 maps to FEAT-005 in sync state
    local sync_state='{"version":"2.0","last_down_sync_at":0,"last_up_sync_at":0,"issues":{"FEAT-005":{"issue_number":99,"last_synced_status":" ","last_remote_state":"open","description_hash":"sha256:def"}}}'
    echo "$sync_state" > "$RALPH_DIR/github-sync-state.json"

    local worker_dir="$RALPH_DIR/workers/worker-FEAT-005-9999999999"
    mkdir -p "$worker_dir"
    echo "$$" > "$worker_dir/agent.pid"

    claim_list_owned() { echo "99"; }

    # Stub gh issue comment to capture the call instead of making API calls
    local captured_issue=""
    gh() {
        if [ "$1" = "issue" ] && [ "$2" = "comment" ]; then
            captured_issue="$3"
        fi
        return 0
    }

    heartbeat_shutdown "$RALPH_DIR" "test-server"

    # If the fallback works, gh issue comment should have been called for issue 99
    # (because the worker dir worker-FEAT-005-* was found after resolving via sync state)
    assert_equals "99" "$captured_issue" \
        "Shutdown should resolve task_id via sync-state and post comment"
}

# =============================================================================
# Run tests
# =============================================================================

run_test test_sync_state_fallback_resolves_task_id
run_test test_sync_state_fallback_skips_when_no_sync_file
run_test test_sync_state_fallback_keeps_cache_result_when_available
run_test test_cache_refresh_failure_logs_warning
run_test test_shutdown_sync_state_fallback

print_test_summary
exit_with_test_result
