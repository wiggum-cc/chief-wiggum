#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/worker/agent-registry.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"

# Source agent-registry (which pulls in its own dependencies)
source "$WIGGUM_HOME/lib/worker/agent-registry.sh"

TEST_DIR=""
MOCK_AGENTS_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    MOCK_AGENTS_DIR="$TEST_DIR/mock-agents"
    mkdir -p "$MOCK_AGENTS_DIR"
    mkdir -p "$TEST_DIR/worker"
    mkdir -p "$TEST_DIR/project/.ralph/logs"

    # Reset loaded agent state
    _LOADED_AGENT=""
    unset -f agent_required_paths agent_run agent_cleanup agent_output_files 2>/dev/null || true
}

teardown() {
    _LOADED_AGENT=""
    unset -f agent_required_paths agent_run agent_cleanup agent_output_files 2>/dev/null || true
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# Helper: Create mock agent scripts
# =============================================================================

create_valid_mock_agent() {
    local agent_name="${1:-mock-agent}"
    cat > "$MOCK_AGENTS_DIR/${agent_name}.sh" << 'EOF'
#!/usr/bin/env bash
# Mock agent for testing

agent_required_paths() {
    echo "prd.md"
    echo "workspace"
}

agent_output_files() {
    echo "results/result.json"
}

agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    return 0
}

agent_cleanup() {
    return 0
}
EOF
}

create_agent_missing_required_paths() {
    local agent_name="${1:-incomplete-agent}"
    cat > "$MOCK_AGENTS_DIR/${agent_name}.sh" << 'EOF'
#!/usr/bin/env bash
# Agent without agent_required_paths

agent_run() {
    return 0
}
EOF
}

create_agent_missing_run() {
    local agent_name="${1:-no-run-agent}"
    cat > "$MOCK_AGENTS_DIR/${agent_name}.sh" << 'EOF'
#!/usr/bin/env bash
# Agent without agent_run

agent_required_paths() {
    echo "prd.md"
}
EOF
}

# =============================================================================
# load_agent() Tests
# =============================================================================

test_load_agent_with_valid_agent_succeeds() {
    create_valid_mock_agent "test-valid"

    # Temporarily override WIGGUM_HOME to point to our mock directory
    local orig_home="$WIGGUM_HOME"
    mkdir -p "$TEST_DIR/fake-home/lib/agents"
    cp "$MOCK_AGENTS_DIR/test-valid.sh" "$TEST_DIR/fake-home/lib/agents/test-valid.sh"
    WIGGUM_HOME="$TEST_DIR/fake-home"

    assert_success "load_agent should succeed for valid agent" load_agent 'test-valid'

    WIGGUM_HOME="$orig_home"
}

test_load_agent_with_nonexistent_agent_fails() {
    assert_failure "load_agent should fail for non-existent agent" \
        load_agent 'nonexistent-agent-xyz'
}

test_load_agent_validates_required_paths_function() {
    create_agent_missing_required_paths "missing-paths"

    local orig_home="$WIGGUM_HOME"
    mkdir -p "$TEST_DIR/fake-home/lib/agents"
    cp "$MOCK_AGENTS_DIR/missing-paths.sh" "$TEST_DIR/fake-home/lib/agents/missing-paths.sh"
    WIGGUM_HOME="$TEST_DIR/fake-home"

    assert_failure "load_agent should fail when agent_required_paths is missing" \
        load_agent 'missing-paths'

    WIGGUM_HOME="$orig_home"
}

test_load_agent_validates_run_function() {
    create_agent_missing_run "no-run"

    local orig_home="$WIGGUM_HOME"
    mkdir -p "$TEST_DIR/fake-home/lib/agents"
    cp "$MOCK_AGENTS_DIR/no-run.sh" "$TEST_DIR/fake-home/lib/agents/no-run.sh"
    WIGGUM_HOME="$TEST_DIR/fake-home"

    assert_failure "load_agent should fail when agent_run is missing" \
        load_agent 'no-run'

    WIGGUM_HOME="$orig_home"
}

# =============================================================================
# validate_agent_prerequisites() Tests
# =============================================================================

test_validate_prerequisites_passes_when_paths_exist() {
    create_valid_mock_agent "prereq-pass"

    local orig_home="$WIGGUM_HOME"
    mkdir -p "$TEST_DIR/fake-home/lib/agents"
    cp "$MOCK_AGENTS_DIR/prereq-pass.sh" "$TEST_DIR/fake-home/lib/agents/prereq-pass.sh"
    WIGGUM_HOME="$TEST_DIR/fake-home"

    load_agent "prereq-pass"

    # Create required paths in worker dir
    local worker_dir="$TEST_DIR/worker-prereq"
    mkdir -p "$worker_dir/workspace"
    echo "test" > "$worker_dir/prd.md"

    assert_success "Should pass when all required paths exist" \
        validate_agent_prerequisites "$worker_dir"

    WIGGUM_HOME="$orig_home"
}

test_validate_prerequisites_fails_when_paths_missing() {
    create_valid_mock_agent "prereq-fail"

    local orig_home="$WIGGUM_HOME"
    mkdir -p "$TEST_DIR/fake-home/lib/agents"
    cp "$MOCK_AGENTS_DIR/prereq-fail.sh" "$TEST_DIR/fake-home/lib/agents/prereq-fail.sh"
    WIGGUM_HOME="$TEST_DIR/fake-home"

    load_agent "prereq-fail"

    # Worker dir with no required paths
    local worker_dir="$TEST_DIR/worker-empty"
    mkdir -p "$worker_dir"

    assert_failure "Should fail when required paths are missing" \
        validate_agent_prerequisites "$worker_dir"

    WIGGUM_HOME="$orig_home"
}

# =============================================================================
# validate_agent_outputs() Tests
# =============================================================================

test_validate_outputs_passes_with_valid_result() {
    create_valid_mock_agent "output-pass"

    local orig_home="$WIGGUM_HOME"
    mkdir -p "$TEST_DIR/fake-home/lib/agents"
    cp "$MOCK_AGENTS_DIR/output-pass.sh" "$TEST_DIR/fake-home/lib/agents/output-pass.sh"
    WIGGUM_HOME="$TEST_DIR/fake-home"

    load_agent "output-pass"

    # Create the expected output file with valid JSON content
    local worker_dir="$TEST_DIR/worker-output-valid"
    mkdir -p "$worker_dir/results"
    echo '{"status": "success", "exit_code": 0}' > "$worker_dir/results/result.json"

    assert_success "Should pass when output files exist and are non-empty" \
        validate_agent_outputs "$worker_dir"

    WIGGUM_HOME="$orig_home"
}

test_validate_outputs_fails_with_missing_result() {
    create_valid_mock_agent "output-fail"

    local orig_home="$WIGGUM_HOME"
    mkdir -p "$TEST_DIR/fake-home/lib/agents"
    cp "$MOCK_AGENTS_DIR/output-fail.sh" "$TEST_DIR/fake-home/lib/agents/output-fail.sh"
    WIGGUM_HOME="$TEST_DIR/fake-home"

    load_agent "output-fail"

    # Worker dir with no output files
    local worker_dir="$TEST_DIR/worker-no-output"
    mkdir -p "$worker_dir/results"

    assert_failure "Should fail when output files are missing" \
        validate_agent_outputs "$worker_dir"

    WIGGUM_HOME="$orig_home"
}

# =============================================================================
# list_agents() Tests
# =============================================================================

test_list_agents_returns_agents() {
    local result
    result=$(list_agents)

    # Should contain at least some known agents
    assert_output_contains "$result" "engineering.software-engineer" \
        "list_agents should include engineering.software-engineer"
}

test_list_agents_includes_system_agents() {
    local result
    result=$(list_agents)

    assert_output_contains "$result" "system.task-worker" \
        "list_agents should include system agent system.task-worker"
}

# =============================================================================
# get_agent_info() Tests - uses a real agent
# =============================================================================

# We test get_agent_info with a real agent since it calls load_agent internally

# =============================================================================
# Run Tests
# =============================================================================

run_test test_load_agent_with_valid_agent_succeeds
run_test test_load_agent_with_nonexistent_agent_fails
run_test test_load_agent_validates_required_paths_function
run_test test_load_agent_validates_run_function
run_test test_validate_prerequisites_passes_when_paths_exist
run_test test_validate_prerequisites_fails_when_paths_missing
run_test test_validate_outputs_passes_with_valid_result
run_test test_validate_outputs_fails_with_missing_result
run_test test_list_agents_returns_agents
run_test test_list_agents_includes_system_agents

print_test_summary
exit_with_test_result
