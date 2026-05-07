#!/usr/bin/env bash
set -euo pipefail
# Tests for config/pipeline-fast.json and engineering.master-followup agent

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"

# Reset the loader guard so we can source it
unset _PIPELINE_LOADER_LOADED
source "$WIGGUM_HOME/lib/pipeline/pipeline-loader.sh"

TEST_DIR=""
setup() {
    TEST_DIR=$(mktemp -d)
    # Reset pipeline state
    _PIPELINE_JSON_FILE=""
    _PIPELINE_JSON=""
    _PIPELINE_STEP_COUNT=0
    PIPELINE_NAME=""
}
teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# pipeline-fast.json Tests
# =============================================================================

test_pipeline_fast_loads_successfully() {
    pipeline_load "$WIGGUM_HOME/config/pipelines/fast.json"
    local rc=$?

    assert_equals "0" "$rc" "pipeline-fast.json should load successfully"
    assert_equals "fast" "$PIPELINE_NAME" "Pipeline name should be 'fast'"
}

test_pipeline_fast_has_five_steps() {
    pipeline_load "$WIGGUM_HOME/config/pipelines/fast.json"

    assert_equals "5" "$(pipeline_step_count)" "Fast pipeline should have 5 steps"
}

test_pipeline_fast_step_ids() {
    pipeline_load "$WIGGUM_HOME/config/pipelines/fast.json"

    assert_equals "planning" "$(pipeline_get 0 ".id")" "Step 0 should be planning"
    assert_equals "execution" "$(pipeline_get 1 ".id")" "Step 1 should be execution"
    assert_equals "summary" "$(pipeline_get 2 ".id")" "Step 2 should be summary"
    assert_equals "master-followup" "$(pipeline_get 3 ".id")" "Step 3 should be master-followup"
    assert_equals "validation" "$(pipeline_get 4 ".id")" "Step 4 should be validation"
}

test_pipeline_fast_agents() {
    pipeline_load "$WIGGUM_HOME/config/pipelines/fast.json"

    assert_equals "product.plan-mode" "$(pipeline_get 0 ".agent")" "Step 0 agent should be product.plan-mode"
    assert_equals "engineering.software-engineer" "$(pipeline_get 1 ".agent")" "Step 1 agent should be engineering.software-engineer"
    assert_equals "general.task-summarizer" "$(pipeline_get 2 ".agent")" "Step 2 agent should be general.task-summarizer"
    assert_equals "engineering.master-followup" "$(pipeline_get 3 ".agent")" "Step 3 agent should be engineering.master-followup"
    assert_equals "engineering.validation-review" "$(pipeline_get 4 ".agent")" "Step 4 agent should be engineering.validation-review"
}

test_pipeline_fast_master_followup_has_fix_handler() {
    pipeline_load "$WIGGUM_HOME/config/pipelines/fast.json"

    local fix_handler
    fix_handler=$(pipeline_get_on_result 3 "FIX")

    assert_output_contains "$fix_handler" "master-followup-fix" "master-followup FIX should have inline agent"
    assert_output_contains "$fix_handler" "engineering.generic-fix" "master-followup FIX should use generic-fix agent"
}

test_pipeline_fast_master_followup_has_max() {
    pipeline_load "$WIGGUM_HOME/config/pipelines/fast.json"

    assert_equals "3" "$(pipeline_get_max 3)" "master-followup step should have max=3"
}

test_pipeline_fast_master_followup_commit_after() {
    pipeline_load "$WIGGUM_HOME/config/pipelines/fast.json"

    assert_equals "true" "$(pipeline_get 3 ".commit_after" "false")" "master-followup should have commit_after=true"
}

test_pipeline_fast_planning_enabled_by() {
    pipeline_load "$WIGGUM_HOME/config/pipelines/fast.json"

    assert_equals "WIGGUM_PLAN_MODE" "$(pipeline_get 0 ".enabled_by")" "planning should be enabled_by WIGGUM_PLAN_MODE"
}

test_pipeline_fast_readonly_steps() {
    pipeline_load "$WIGGUM_HOME/config/pipelines/fast.json"

    assert_equals "true" "$(pipeline_get 0 ".readonly" "false")" "planning should be readonly"
    assert_equals "true" "$(pipeline_get 2 ".readonly" "false")" "summary should be readonly"
    assert_equals "true" "$(pipeline_get 4 ".readonly" "false")" "validation should be readonly"
}

# =============================================================================
# master-followup.md Agent Tests
# =============================================================================

test_master_followup_md_exists() {
    local md_file="$WIGGUM_HOME/lib/agents/engineering/master-followup.md"

    if [ -f "$md_file" ]; then
        assert_success "master-followup.md should exist" true
    else
        assert_failure "master-followup.md should exist" true
    fi
}

test_master_followup_md_loads() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local md_file="$WIGGUM_HOME/lib/agents/engineering/master-followup.md"

    if md_agent_load "$md_file"; then
        assert_equals "engineering.master-followup" "$_MD_TYPE" "master-followup.md should have correct type"
    else
        assert_failure "master-followup.md should load successfully" true
    fi
}

test_master_followup_md_mode() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local md_file="$WIGGUM_HOME/lib/agents/engineering/master-followup.md"
    md_agent_load "$md_file"

    assert_equals "ralph_loop" "$_MD_MODE" "master-followup.md should be ralph_loop mode"
}

test_master_followup_md_readonly() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local md_file="$WIGGUM_HOME/lib/agents/engineering/master-followup.md"
    md_agent_load "$md_file"

    assert_equals "false" "$_MD_READONLY" "master-followup.md should not be readonly"
}

test_master_followup_md_valid_results() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local md_file="$WIGGUM_HOME/lib/agents/engineering/master-followup.md"
    md_agent_load "$md_file"

    local result_count=${#_MD_VALID_RESULTS[@]}
    if [ "$result_count" -eq 4 ]; then
        assert_success "master-followup.md should have 4 valid results (PASS, FIX, FAIL, SKIP)" true
    else
        assert_failure "master-followup.md should have 4 valid results, got $result_count" true
    fi
}

test_master_followup_md_has_system_prompt() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local md_file="$WIGGUM_HOME/lib/agents/engineering/master-followup.md"
    md_agent_load "$md_file"

    if echo "$_MD_SYSTEM_PROMPT" | grep -q "MASTER FOLLOWUP AGENT"; then
        assert_success "master-followup.md should have MASTER FOLLOWUP AGENT in system prompt" true
    else
        assert_failure "master-followup.md should have MASTER FOLLOWUP AGENT in system prompt" true
    fi
}

test_master_followup_md_has_three_phases() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local md_file="$WIGGUM_HOME/lib/agents/engineering/master-followup.md"
    md_agent_load "$md_file"

    local has_security has_test has_docs
    has_security=false
    has_test=false
    has_docs=false

    if echo "$_MD_USER_PROMPT" | grep -q "PHASE 1: SECURITY AUDIT"; then
        has_security=true
    fi
    if echo "$_MD_USER_PROMPT" | grep -q "PHASE 2: TEST COVERAGE"; then
        has_test=true
    fi
    if echo "$_MD_USER_PROMPT" | grep -q "PHASE 3: DOCUMENTATION"; then
        has_docs=true
    fi

    if [ "$has_security" = true ] && [ "$has_test" = true ] && [ "$has_docs" = true ]; then
        assert_success "master-followup.md should have all three phases" true
    else
        assert_failure "master-followup.md should have all three phases (security=$has_security, test=$has_test, docs=$has_docs)" true
    fi
}

test_master_followup_md_has_continuation_prompt() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local md_file="$WIGGUM_HOME/lib/agents/engineering/master-followup.md"
    md_agent_load "$md_file"

    if echo "$_MD_CONTINUATION_PROMPT" | grep -q "CONTINUATION CONTEXT"; then
        assert_success "master-followup.md should have continuation prompt" true
    else
        assert_failure "master-followup.md should have continuation prompt" true
    fi
}

# =============================================================================
# agents.json Config Tests
# =============================================================================

test_agents_json_has_master_followup() {
    local config_file="$WIGGUM_HOME/config/agents.json"

    if jq -e '.agents["engineering.master-followup"]' "$config_file" >/dev/null 2>&1; then
        assert_success "agents.json should have engineering.master-followup entry" true
    else
        assert_failure "agents.json should have engineering.master-followup entry" true
    fi
}

test_agents_json_master_followup_max_iterations() {
    local config_file="$WIGGUM_HOME/config/agents.json"

    local max_iterations
    max_iterations=$(jq -r '.agents["engineering.master-followup"].max_iterations' "$config_file")

    assert_equals "10" "$max_iterations" "master-followup max_iterations should be 10"
}

test_agents_json_master_followup_max_turns() {
    local config_file="$WIGGUM_HOME/config/agents.json"

    local max_turns
    max_turns=$(jq -r '.agents["engineering.master-followup"].max_turns' "$config_file")

    assert_equals "100" "$max_turns" "master-followup max_turns should be 100"
}

test_agents_json_master_followup_result_mappings() {
    local config_file="$WIGGUM_HOME/config/agents.json"

    local pass_status fail_status fix_status skip_status
    pass_status=$(jq -r '.agents["engineering.master-followup"].result_mappings.PASS.status' "$config_file")
    fail_status=$(jq -r '.agents["engineering.master-followup"].result_mappings.FAIL.status' "$config_file")
    fix_status=$(jq -r '.agents["engineering.master-followup"].result_mappings.FIX.status' "$config_file")
    skip_status=$(jq -r '.agents["engineering.master-followup"].result_mappings.SKIP.status' "$config_file")

    assert_equals "success" "$pass_status" "PASS should map to success"
    assert_equals "failure" "$fail_status" "FAIL should map to failure"
    assert_equals "partial" "$fix_status" "FIX should map to partial"
    assert_equals "success" "$skip_status" "SKIP should map to success"
}

test_agents_json_master_followup_exit_codes() {
    local config_file="$WIGGUM_HOME/config/agents.json"

    local pass_code fail_code fix_code skip_code
    pass_code=$(jq -r '.agents["engineering.master-followup"].result_mappings.PASS.exit_code' "$config_file")
    fail_code=$(jq -r '.agents["engineering.master-followup"].result_mappings.FAIL.exit_code' "$config_file")
    fix_code=$(jq -r '.agents["engineering.master-followup"].result_mappings.FIX.exit_code' "$config_file")
    skip_code=$(jq -r '.agents["engineering.master-followup"].result_mappings.SKIP.exit_code' "$config_file")

    assert_equals "0" "$pass_code" "PASS exit_code should be 0"
    assert_equals "10" "$fail_code" "FAIL exit_code should be 10"
    assert_equals "0" "$fix_code" "FIX exit_code should be 0"
    assert_equals "0" "$skip_code" "SKIP exit_code should be 0"
}

test_agents_json_master_followup_default_jumps() {
    local config_file="$WIGGUM_HOME/config/agents.json"

    local pass_jump fail_jump fix_jump skip_jump
    pass_jump=$(jq -r '.agents["engineering.master-followup"].result_mappings.PASS.default_jump' "$config_file")
    fail_jump=$(jq -r '.agents["engineering.master-followup"].result_mappings.FAIL.default_jump' "$config_file")
    fix_jump=$(jq -r '.agents["engineering.master-followup"].result_mappings.FIX.default_jump' "$config_file")
    skip_jump=$(jq -r '.agents["engineering.master-followup"].result_mappings.SKIP.default_jump' "$config_file")

    assert_equals "next" "$pass_jump" "PASS default_jump should be next"
    assert_equals "abort" "$fail_jump" "FAIL default_jump should be abort"
    assert_equals "prev" "$fix_jump" "FIX default_jump should be prev"
    assert_equals "next" "$skip_jump" "SKIP default_jump should be next"
}

# =============================================================================
# Run Tests
# =============================================================================

# pipeline-fast.json tests
run_test test_pipeline_fast_loads_successfully
run_test test_pipeline_fast_has_five_steps
run_test test_pipeline_fast_step_ids
run_test test_pipeline_fast_agents
run_test test_pipeline_fast_master_followup_has_fix_handler
run_test test_pipeline_fast_master_followup_has_max
run_test test_pipeline_fast_master_followup_commit_after
run_test test_pipeline_fast_planning_enabled_by
run_test test_pipeline_fast_readonly_steps

# master-followup.md tests
run_test test_master_followup_md_exists
run_test test_master_followup_md_loads
run_test test_master_followup_md_mode
run_test test_master_followup_md_readonly
run_test test_master_followup_md_valid_results
run_test test_master_followup_md_has_system_prompt
run_test test_master_followup_md_has_three_phases
run_test test_master_followup_md_has_continuation_prompt

# agents.json tests
run_test test_agents_json_has_master_followup
run_test test_agents_json_master_followup_max_iterations
run_test test_agents_json_master_followup_max_turns
run_test test_agents_json_master_followup_result_mappings
run_test test_agents_json_master_followup_exit_codes
run_test test_agents_json_master_followup_default_jumps

print_test_summary
exit_with_test_result
