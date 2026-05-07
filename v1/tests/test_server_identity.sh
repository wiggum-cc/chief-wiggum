#!/usr/bin/env bash
# test_server_identity.sh - Tests for distributed server identity management
set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

# =============================================================================
# Setup/Teardown
# =============================================================================

setup() {
    TEST_RALPH_DIR=$(mktemp -d)
    mkdir -p "$TEST_RALPH_DIR/server"
}

teardown() {
    rm -rf "$TEST_RALPH_DIR"
    unset WIGGUM_SERVER_ID
}

# =============================================================================
# Server ID Generation Tests
# =============================================================================

test_server_identity_generate_format() {
    local server_id
    server_id=$(server_identity_generate)

    # Format: {hostname}-{random}
    if [[ "$server_id" =~ ^[a-z0-9].*-[a-f0-9]+$ ]]; then
        echo -e "  ${GREEN}✓${NC} Server ID has correct format: $server_id"
    else
        echo -e "  ${RED}✗${NC} Server ID has wrong format: $server_id"
        echo "    Expected pattern: {hostname}-{random}"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_server_identity_generate_unique() {
    local id1 id2
    id1=$(server_identity_generate)
    sleep 0.1
    id2=$(server_identity_generate)

    assert_not_equals "$id1" "$id2" "Generated IDs should be unique"
}

test_server_identity_generate_contains_hostname() {
    local server_id hostname_part
    server_id=$(server_identity_generate)

    # Extract hostname (everything before the last dash-separated hex segment)
    hostname_part=$(echo "$server_id" | sed 's/-[a-f0-9]*$//' )

    if [ -n "$hostname_part" ]; then
        echo -e "  ${GREEN}✓${NC} Server ID contains hostname part: $hostname_part"
    else
        echo -e "  ${RED}✗${NC} Server ID missing hostname: $server_id"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Server Identity Persistence Tests
# =============================================================================

test_server_identity_get_or_create_creates_file() {
    server_identity_get_or_create "$TEST_RALPH_DIR" > /dev/null

    assert_file_exists "$TEST_RALPH_DIR/server/identity.json" \
        "Identity file should be created"
}

test_server_identity_get_or_create_valid_json() {
    server_identity_get_or_create "$TEST_RALPH_DIR" > /dev/null

    local identity_file="$TEST_RALPH_DIR/server/identity.json"

    if jq -e . "$identity_file" > /dev/null 2>&1; then
        echo -e "  ${GREEN}✓${NC} Identity file contains valid JSON"
    else
        echo -e "  ${RED}✗${NC} Identity file contains invalid JSON"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_server_identity_get_or_create_has_required_fields() {
    server_identity_get_or_create "$TEST_RALPH_DIR" > /dev/null

    local identity_file="$TEST_RALPH_DIR/server/identity.json"
    local server_id started_at hostname_field

    server_id=$(jq -r '.server_id // empty' "$identity_file")
    started_at=$(jq -r '.started_at // empty' "$identity_file")
    hostname_field=$(jq -r '.hostname // empty' "$identity_file")

    if [ -n "$server_id" ]; then
        echo -e "  ${GREEN}✓${NC} Identity has server_id: $server_id"
    else
        echo -e "  ${RED}✗${NC} Identity missing server_id"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if [ -n "$started_at" ]; then
        echo -e "  ${GREEN}✓${NC} Identity has started_at: $started_at"
    else
        echo -e "  ${RED}✗${NC} Identity missing started_at"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if [ -n "$hostname_field" ]; then
        echo -e "  ${GREEN}✓${NC} Identity has hostname: $hostname_field"
    else
        echo -e "  ${RED}✗${NC} Identity missing hostname"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_server_identity_get_or_create_reuses_existing() {
    # Create identity first
    local first_id
    first_id=$(server_identity_get_or_create "$TEST_RALPH_DIR")

    # Reinit should reuse existing
    local second_id
    second_id=$(server_identity_get_or_create "$TEST_RALPH_DIR")

    assert_equals "$first_id" "$second_id" "Should reuse existing server ID"
}

test_server_identity_get() {
    # Create first
    local created_id
    created_id=$(server_identity_get_or_create "$TEST_RALPH_DIR")

    # Get should return same ID
    local got_id
    got_id=$(server_identity_get "$TEST_RALPH_DIR")

    assert_equals "$created_id" "$got_id" "Get should return created ID"
}

test_server_identity_get_returns_empty_when_none() {
    local empty_dir
    empty_dir=$(mktemp -d)

    local result
    result=$(server_identity_get "$empty_dir")

    assert_equals "" "$result" "Should return empty when no identity exists"

    rm -rf "$empty_dir"
}

test_server_identity_respects_override() {
    export WIGGUM_SERVER_ID="custom-server-123"

    # source the file again to pick up the override
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

    local server_id
    server_id=$(server_identity_get_or_create "$TEST_RALPH_DIR")

    assert_equals "custom-server-123" "$server_id" "Should use override server ID"
}

# =============================================================================
# Server Config Tests
# =============================================================================

test_server_config_load_defaults() {
    server_identity_get_or_create "$TEST_RALPH_DIR" > /dev/null
    server_config_load "$TEST_RALPH_DIR"

    # Check that config variables are set
    if [ -n "${SERVER_HEARTBEAT_INTERVAL:-}" ]; then
        echo -e "  ${GREEN}✓${NC} SERVER_HEARTBEAT_INTERVAL set: $SERVER_HEARTBEAT_INTERVAL"
    else
        echo -e "  ${RED}✗${NC} SERVER_HEARTBEAT_INTERVAL not set"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if [ -n "${SERVER_STALE_THRESHOLD:-}" ]; then
        echo -e "  ${GREEN}✓${NC} SERVER_STALE_THRESHOLD set: $SERVER_STALE_THRESHOLD"
    else
        echo -e "  ${RED}✗${NC} SERVER_STALE_THRESHOLD not set"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_server_config_load_from_file() {
    server_identity_get_or_create "$TEST_RALPH_DIR" > /dev/null

    # Create custom config
    cat > "$TEST_RALPH_DIR/server/config.json" << 'EOF'
{
    "polling": {
        "sync_interval_seconds": 120,
        "heartbeat_interval_seconds": 60
    },
    "claims": {
        "max_concurrent_tasks": 8,
        "stale_threshold_seconds": 300
    }
}
EOF

    server_config_load "$TEST_RALPH_DIR"

    assert_equals "60" "$SERVER_HEARTBEAT_INTERVAL" "Should load heartbeat interval from config"
    assert_equals "300" "$SERVER_STALE_THRESHOLD" "Should load stale threshold from config"
    assert_equals "8" "$SERVER_MAX_CONCURRENT" "Should load max concurrent from config"
}

# =============================================================================
# Server Claims Cache Tests
# =============================================================================

test_server_claims_update_add() {
    server_identity_get_or_create "$TEST_RALPH_DIR" > /dev/null

    server_claims_update "$TEST_RALPH_DIR" "TASK-001" "add"

    local claims_file="$TEST_RALPH_DIR/server/claims.json"
    assert_file_exists "$claims_file" "Claims file should exist"

    # Claims are stored as .tasks object, not .claims array
    if jq -e '.tasks["TASK-001"]' "$claims_file" > /dev/null 2>&1; then
        echo -e "  ${GREEN}✓${NC} TASK-001 added to claims"
    else
        echo -e "  ${RED}✗${NC} TASK-001 not in claims"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_server_claims_update_remove() {
    server_identity_get_or_create "$TEST_RALPH_DIR" > /dev/null

    # Add then remove
    server_claims_update "$TEST_RALPH_DIR" "TASK-001" "add"
    server_claims_update "$TEST_RALPH_DIR" "TASK-001" "remove"

    local claims_file="$TEST_RALPH_DIR/server/claims.json"

    # Claims are stored as .tasks object
    if ! jq -e '.tasks["TASK-001"]' "$claims_file" > /dev/null 2>&1; then
        echo -e "  ${GREEN}✓${NC} TASK-001 removed from claims"
    else
        echo -e "  ${RED}✗${NC} TASK-001 still in claims"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_server_claims_list() {
    server_identity_get_or_create "$TEST_RALPH_DIR" > /dev/null

    server_claims_update "$TEST_RALPH_DIR" "TASK-001" "add"
    server_claims_update "$TEST_RALPH_DIR" "TASK-002" "add"

    local claims
    claims=$(server_claims_list "$TEST_RALPH_DIR")

    assert_output_contains "$claims" "TASK-001" "Should list TASK-001"
    assert_output_contains "$claims" "TASK-002" "Should list TASK-002"
}

test_server_claims_has() {
    server_identity_get_or_create "$TEST_RALPH_DIR" > /dev/null

    server_claims_update "$TEST_RALPH_DIR" "TASK-001" "add"

    assert_success "Should have TASK-001" \
        server_claims_has "$TEST_RALPH_DIR" "TASK-001"

    assert_failure "Should not have TASK-999" \
        server_claims_has "$TEST_RALPH_DIR" "TASK-999"
}

# =============================================================================
# Run Tests
# =============================================================================

echo "=== Server Identity Tests ==="
run_test test_server_identity_generate_format
run_test test_server_identity_generate_unique
run_test test_server_identity_generate_contains_hostname
run_test test_server_identity_get_or_create_creates_file
run_test test_server_identity_get_or_create_valid_json
run_test test_server_identity_get_or_create_has_required_fields
run_test test_server_identity_get_or_create_reuses_existing
run_test test_server_identity_get
run_test test_server_identity_get_returns_empty_when_none
run_test test_server_identity_respects_override
run_test test_server_config_load_defaults
run_test test_server_config_load_from_file
run_test test_server_claims_update_add
run_test test_server_claims_update_remove
run_test test_server_claims_list
run_test test_server_claims_has

print_test_summary
exit_with_test_result
