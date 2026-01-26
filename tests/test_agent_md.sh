#!/usr/bin/env bash
# Test suite for declarative markdown agent parser (lib/core/agent-md.sh)
# Tests: frontmatter parsing, section extraction, variable interpolation, mode detection

set -euo pipefail

# Get the script directory and project root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Source the test framework
source "$SCRIPT_DIR/test-framework.sh"

# Setup WIGGUM_HOME for tests
export WIGGUM_HOME="$PROJECT_ROOT"

# =============================================================================
# Test Fixtures
# =============================================================================

# Create a minimal markdown agent fixture
_create_test_agent_md() {
    local tmpdir="$1"
    local agent_file="$tmpdir/test-agent.md"

    cat > "$agent_file" << 'EOF'
---
type: engineering.test-agent
description: Test agent for unit tests
required_paths: [workspace, prd.md]
valid_results: [PASS, FAIL, FIX]
mode: ralph_loop
readonly: true
report_tag: report
result_tag: result
outputs: [session_id, report_file]
---

<WIGGUM_SYSTEM_PROMPT>
TEST AGENT SYSTEM PROMPT:

WORKSPACE: {{workspace}}
WORKER_DIR: {{worker_dir}}
PROJECT_DIR: {{project_dir}}
TASK_ID: {{task_id}}

{{git_restrictions}}
</WIGGUM_SYSTEM_PROMPT>

<WIGGUM_USER_PROMPT>
{{context_section}}

USER PROMPT CONTENT:
Step ID: {{step_id}}
Run ID: {{run_id}}
</WIGGUM_USER_PROMPT>

<WIGGUM_CONTINUATION_PROMPT>
CONTINUATION (Iteration {{iteration}}):
Previous iteration: {{prev_iteration}}
Output dir: {{output_dir}}
</WIGGUM_CONTINUATION_PROMPT>
EOF

    echo "$agent_file"
}

# Create a once-mode agent fixture
_create_once_agent_md() {
    local tmpdir="$1"
    local agent_file="$tmpdir/once-agent.md"

    cat > "$agent_file" << 'EOF'
---
type: product.once-agent
description: Once-mode test agent
required_paths: [workspace]
valid_results: [PASS, SKIP]
mode: once
readonly: false
---

<WIGGUM_SYSTEM_PROMPT>
ONCE MODE SYSTEM PROMPT
</WIGGUM_SYSTEM_PROMPT>

<WIGGUM_USER_PROMPT>
ONCE MODE USER PROMPT
</WIGGUM_USER_PROMPT>
EOF

    echo "$agent_file"
}

# Create a resume-mode agent fixture
_create_resume_agent_md() {
    local tmpdir="$1"
    local agent_file="$tmpdir/resume-agent.md"

    cat > "$agent_file" << 'EOF'
---
type: system.resume-agent
description: Resume-mode test agent
required_paths: [workspace]
valid_results: [PASS, SKIP]
mode: resume
session_from: parent
output_path: summaries/summary.txt
---

<WIGGUM_USER_PROMPT>
RESUME MODE USER PROMPT
Parent session: {{parent.session_id}}
</WIGGUM_USER_PROMPT>
EOF

    echo "$agent_file"
}

# =============================================================================
# Test: Syntax Validation
# =============================================================================

test_agent_md_sh_syntax() {
    if bash -n "$WIGGUM_HOME/lib/core/agent-md.sh" 2>/dev/null; then
        assert_success "agent-md.sh should have valid bash syntax" true
    else
        assert_failure "agent-md.sh should have valid bash syntax" true
    fi
}

# =============================================================================
# Test: Frontmatter Parsing
# =============================================================================

test_parse_frontmatter_type() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    assert_equals "engineering.test-agent" "$_MD_TYPE" "Should parse type from frontmatter"

    rm -rf "$tmpdir"
}

test_parse_frontmatter_description() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    assert_equals "Test agent for unit tests" "$_MD_DESCRIPTION" "Should parse description from frontmatter"

    rm -rf "$tmpdir"
}

test_parse_frontmatter_mode() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    assert_equals "ralph_loop" "$_MD_MODE" "Should parse mode from frontmatter"

    rm -rf "$tmpdir"
}

test_parse_frontmatter_readonly() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    assert_equals "true" "$_MD_READONLY" "Should parse readonly from frontmatter"

    rm -rf "$tmpdir"
}

test_parse_frontmatter_required_paths() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    local path_count=${#_MD_REQUIRED_PATHS[@]}
    if [ "$path_count" -ge 2 ]; then
        assert_success "Should parse required_paths array (got $path_count items)" true
    else
        assert_failure "Should parse required_paths array (got $path_count items)" true
    fi

    rm -rf "$tmpdir"
}

test_parse_frontmatter_valid_results() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    local result_count=${#_MD_VALID_RESULTS[@]}
    if [ "$result_count" -ge 3 ]; then
        assert_success "Should parse valid_results array (got $result_count items)" true
    else
        assert_failure "Should parse valid_results array (got $result_count items)" true
    fi

    rm -rf "$tmpdir"
}

# =============================================================================
# Test: Section Extraction
# =============================================================================

test_extract_system_prompt() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    if echo "$_MD_SYSTEM_PROMPT" | grep -q "TEST AGENT SYSTEM PROMPT"; then
        assert_success "Should extract system prompt section" true
    else
        assert_failure "Should extract system prompt section" true
    fi

    rm -rf "$tmpdir"
}

test_extract_user_prompt() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    if echo "$_MD_USER_PROMPT" | grep -q "USER PROMPT CONTENT"; then
        assert_success "Should extract user prompt section" true
    else
        assert_failure "Should extract user prompt section" true
    fi

    rm -rf "$tmpdir"
}

test_extract_continuation_prompt() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    if echo "$_MD_CONTINUATION_PROMPT" | grep -q "CONTINUATION"; then
        assert_success "Should extract continuation prompt section" true
    else
        assert_failure "Should extract continuation prompt section" true
    fi

    rm -rf "$tmpdir"
}

# =============================================================================
# Test: Variable Interpolation
# =============================================================================

test_interpolate_path_variables() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    # Set runtime context
    _MD_WORKSPACE="/test/workspace"
    _MD_WORKER_DIR="/test/worker"
    _MD_PROJECT_DIR="/test/project"

    local result
    result=$(_md_interpolate "{{workspace}} and {{worker_dir}} and {{project_dir}}")

    if echo "$result" | grep -q "/test/workspace and /test/worker and /test/project"; then
        assert_success "Should interpolate path variables" true
    else
        assert_failure "Should interpolate path variables (got: $result)" true
    fi

    rm -rf "$tmpdir"
}

test_interpolate_task_context() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    # Set runtime context
    _MD_TASK_ID="TASK-001"
    export WIGGUM_STEP_ID="test-step"

    local result
    result=$(_md_interpolate "task={{task_id}} step={{step_id}}")

    if echo "$result" | grep -q "task=TASK-001 step=test-step"; then
        assert_success "Should interpolate task context variables" true
    else
        assert_failure "Should interpolate task context variables (got: $result)" true
    fi

    unset WIGGUM_STEP_ID
    rm -rf "$tmpdir"
}

test_interpolate_iteration_variables() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    local result
    result=$(_md_interpolate_iteration "iter={{iteration}} prev={{prev_iteration}}" "5" "/output")

    if echo "$result" | grep -q "iter=5 prev=4"; then
        assert_success "Should interpolate iteration variables" true
    else
        assert_failure "Should interpolate iteration variables (got: $result)" true
    fi

    rm -rf "$tmpdir"
}

# =============================================================================
# Test: Mode Detection
# =============================================================================

test_once_mode_detection() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_once_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    assert_equals "once" "$_MD_MODE" "Should detect once mode"

    rm -rf "$tmpdir"
}

test_resume_mode_detection() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_resume_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    assert_equals "resume" "$_MD_MODE" "Should detect resume mode"
    assert_equals "parent" "$_MD_SESSION_FROM" "Should parse session_from"

    rm -rf "$tmpdir"
}

# =============================================================================
# Test: Agent Interface Generation
# =============================================================================

test_md_agent_init_defines_functions() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    # Clear any existing functions
    unset -f agent_required_paths agent_run 2>/dev/null || true

    md_agent_init "$agent_file" "engineering.test-agent"

    # Check that required functions are defined
    if type agent_required_paths &>/dev/null; then
        assert_success "md_agent_init should define agent_required_paths" true
    else
        assert_failure "md_agent_init should define agent_required_paths" true
    fi

    if type agent_run &>/dev/null; then
        assert_success "md_agent_init should define agent_run" true
    else
        assert_failure "md_agent_init should define agent_run" true
    fi

    rm -rf "$tmpdir"
}

test_agent_required_paths_returns_paths() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_init "$agent_file" "engineering.test-agent"

    local paths
    paths=$(agent_required_paths)

    if echo "$paths" | grep -q "workspace"; then
        assert_success "agent_required_paths should return workspace" true
    else
        assert_failure "agent_required_paths should return workspace (got: $paths)" true
    fi

    rm -rf "$tmpdir"
}

# =============================================================================
# Test: Validation
# =============================================================================

test_load_fails_on_missing_file() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    if md_agent_load "/nonexistent/path/agent.md" 2>/dev/null; then
        assert_failure "Should fail on missing file" true
    else
        assert_success "Should fail on missing file" true
    fi
}

test_load_fails_on_missing_type() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file="$tmpdir/invalid.md"

    cat > "$agent_file" << 'EOF'
---
description: Missing type field
required_paths: [workspace]
valid_results: [PASS]
mode: once
---

<WIGGUM_SYSTEM_PROMPT>
System
</WIGGUM_SYSTEM_PROMPT>

<WIGGUM_USER_PROMPT>
User
</WIGGUM_USER_PROMPT>
EOF

    if md_agent_load "$agent_file" 2>/dev/null; then
        assert_failure "Should fail on missing type field" true
    else
        assert_success "Should fail on missing type field" true
    fi

    rm -rf "$tmpdir"
}

test_load_fails_on_missing_user_prompt() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file="$tmpdir/invalid.md"

    cat > "$agent_file" << 'EOF'
---
type: test.invalid
description: Missing user prompt
required_paths: [workspace]
valid_results: [PASS]
mode: once
---

<WIGGUM_SYSTEM_PROMPT>
System only
</WIGGUM_SYSTEM_PROMPT>
EOF

    if md_agent_load "$agent_file" 2>/dev/null; then
        assert_failure "Should fail on missing user prompt" true
    else
        assert_success "Should fail on missing user prompt" true
    fi

    rm -rf "$tmpdir"
}

# =============================================================================
# Test: Supervisor Integration
# =============================================================================

test_parse_frontmatter_supervisor_interval() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file="$tmpdir/supervised-agent.md"

    cat > "$agent_file" << 'EOF'
---
type: test.supervised-agent
description: Agent with supervisor interval
required_paths: [workspace]
valid_results: [PASS, FAIL]
mode: ralph_loop
supervisor_interval: 3
---

<WIGGUM_SYSTEM_PROMPT>
System prompt
</WIGGUM_SYSTEM_PROMPT>

<WIGGUM_USER_PROMPT>
User prompt
</WIGGUM_USER_PROMPT>
EOF

    md_agent_load "$agent_file"

    assert_equals "3" "$_MD_SUPERVISOR_INTERVAL" "Should parse supervisor_interval from frontmatter"

    rm -rf "$tmpdir"
}

test_supervisor_feedback_interpolation() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file
    agent_file=$(_create_test_agent_md "$tmpdir")

    md_agent_load "$agent_file"

    # Set supervisor feedback
    _MD_SUPERVISOR_FEEDBACK="Focus on error handling"

    local result
    result=$(_md_interpolate_iteration "Supervisor says: {{supervisor_feedback}}" "1" "/output")

    if echo "$result" | grep -q "Supervisor says: Focus on error handling"; then
        assert_success "Should interpolate supervisor_feedback variable" true
    else
        assert_failure "Should interpolate supervisor_feedback variable (got: $result)" true
    fi

    rm -rf "$tmpdir"
}

# =============================================================================
# Test: Plan File Support
# =============================================================================

test_parse_frontmatter_plan_file() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    local agent_file="$tmpdir/plan-agent.md"

    cat > "$agent_file" << 'EOF'
---
type: test.plan-agent
description: Agent with plan file
required_paths: [workspace]
valid_results: [PASS, FAIL]
mode: ralph_loop
plan_file: "{{ralph_dir}}/plans/{{task_id}}.md"
---

<WIGGUM_SYSTEM_PROMPT>
System prompt
</WIGGUM_SYSTEM_PROMPT>

<WIGGUM_USER_PROMPT>
User prompt
</WIGGUM_USER_PROMPT>
EOF

    md_agent_load "$agent_file"

    assert_equals "{{ralph_dir}}/plans/{{task_id}}.md" "$_MD_PLAN_FILE" "Should parse plan_file from frontmatter"

    rm -rf "$tmpdir"
}

test_plan_section_generation() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)

    # Create a mock plan file
    mkdir -p "$tmpdir/plans"
    echo "# Implementation Plan" > "$tmpdir/plans/TEST-001.md"

    # Set context for interpolation
    _MD_PROJECT_DIR="$tmpdir"
    _MD_TASK_ID="TEST-001"
    _MD_PLAN_FILE="{{ralph_dir}}/plans/{{task_id}}.md"
    export RALPH_DIR="$tmpdir"

    local result
    result=$(_md_generate_plan_section)

    if echo "$result" | grep -q "IMPLEMENTATION PLAN AVAILABLE"; then
        assert_success "Should generate plan section when plan file exists" true
    else
        assert_failure "Should generate plan section when plan file exists (got: $result)" true
    fi

    unset RALPH_DIR
    rm -rf "$tmpdir"
}

test_plan_section_empty_when_no_file() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)

    _MD_PROJECT_DIR="$tmpdir"
    _MD_TASK_ID="TEST-001"
    _MD_PLAN_FILE=""

    local result
    result=$(_md_generate_plan_section)

    if [ -z "$result" ]; then
        assert_success "Should return empty when no plan file specified" true
    else
        assert_failure "Should return empty when no plan file specified (got: $result)" true
    fi

    rm -rf "$tmpdir"
}

# =============================================================================
# Test: Conditional Section Processing
# =============================================================================

test_conditional_supervisor_with_feedback() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    _MD_SUPERVISOR_FEEDBACK="Some feedback"

    local template="Before
<WIGGUM_IF_SUPERVISOR>
GUIDANCE: {{supervisor_feedback}}
</WIGGUM_IF_SUPERVISOR>
After"

    local result
    result=$(_md_process_conditionals "$template" "1")

    if echo "$result" | grep -q "GUIDANCE:"; then
        assert_success "Should include supervisor section when feedback present" true
    else
        assert_failure "Should include supervisor section when feedback present (got: $result)" true
    fi
}

test_conditional_supervisor_without_feedback() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    _MD_SUPERVISOR_FEEDBACK=""

    local template="Before
<WIGGUM_IF_SUPERVISOR>
GUIDANCE: hidden
</WIGGUM_IF_SUPERVISOR>
After"

    local result
    result=$(_md_process_conditionals "$template" "1")

    if echo "$result" | grep -q "GUIDANCE:"; then
        assert_failure "Should exclude supervisor section when no feedback" true
    else
        assert_success "Should exclude supervisor section when no feedback" true
    fi
}

test_conditional_iteration_zero() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    _MD_SUPERVISOR_FEEDBACK=""

    local template="<WIGGUM_IF_ITERATION_ZERO>
First iteration content
</WIGGUM_IF_ITERATION_ZERO>
<WIGGUM_IF_ITERATION_NONZERO>
Later iteration content
</WIGGUM_IF_ITERATION_NONZERO>"

    local result
    result=$(_md_process_conditionals "$template" "0")

    if echo "$result" | grep -q "First iteration content" && ! echo "$result" | grep -q "Later iteration content"; then
        assert_success "Should show only iteration zero content on iteration 0" true
    else
        assert_failure "Should show only iteration zero content on iteration 0 (got: $result)" true
    fi
}

test_conditional_iteration_nonzero() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    _MD_SUPERVISOR_FEEDBACK=""

    local template="<WIGGUM_IF_ITERATION_ZERO>
First iteration content
</WIGGUM_IF_ITERATION_ZERO>
<WIGGUM_IF_ITERATION_NONZERO>
Later iteration content
</WIGGUM_IF_ITERATION_NONZERO>"

    local result
    result=$(_md_process_conditionals "$template" "3")

    if echo "$result" | grep -q "Later iteration content" && ! echo "$result" | grep -q "First iteration content"; then
        assert_success "Should show only nonzero content on iteration > 0" true
    else
        assert_failure "Should show only nonzero content on iteration > 0 (got: $result)" true
    fi
}

test_conditional_file_exists() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local tmpdir
    tmpdir=$(mktemp -d)

    # Create a test file
    echo "test" > "$tmpdir/exists.txt"

    _MD_WORKER_DIR="$tmpdir"

    local template="<WIGGUM_IF_FILE_EXISTS:{{worker_dir}}/exists.txt>
File content
</WIGGUM_IF_FILE_EXISTS>
<WIGGUM_IF_FILE_EXISTS:{{worker_dir}}/missing.txt>
Missing content
</WIGGUM_IF_FILE_EXISTS>"

    local result
    result=$(_md_process_conditionals "$template" "0")

    if echo "$result" | grep -q "File content" && ! echo "$result" | grep -q "Missing content"; then
        assert_success "Should show content only when file exists" true
    else
        assert_failure "Should show content only when file exists (got: $result)" true
    fi

    rm -rf "$tmpdir"
}

# =============================================================================
# Test: Task Executor MD
# =============================================================================

test_task_executor_md_loads() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local md_file="$WIGGUM_HOME/lib/agents/system/task-executor.md"

    if [ ! -f "$md_file" ]; then
        skip_test "task-executor.md not found"
        return
    fi

    if md_agent_load "$md_file"; then
        assert_equals "system.task-executor" "$_MD_TYPE" "task-executor.md should have correct type"
        assert_equals "ralph_loop" "$_MD_MODE" "task-executor.md should be ralph_loop mode"
        assert_equals "2" "$_MD_SUPERVISOR_INTERVAL" "task-executor.md should have supervisor_interval=2"
    else
        assert_failure "task-executor.md should load successfully" true
    fi
}

# =============================================================================
# Test: Real Agent Files
# =============================================================================

test_security_audit_md_loads() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local md_file="$WIGGUM_HOME/lib/agents/engineering/security-audit.md"

    if [ ! -f "$md_file" ]; then
        skip_test "security-audit.md not found"
        return
    fi

    if md_agent_load "$md_file"; then
        assert_equals "engineering.security-audit" "$_MD_TYPE" "security-audit.md should have correct type"
        assert_equals "ralph_loop" "$_MD_MODE" "security-audit.md should be ralph_loop mode"
        assert_equals "true" "$_MD_READONLY" "security-audit.md should be readonly"
    else
        assert_failure "security-audit.md should load successfully" true
    fi
}

test_validation_review_md_loads() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local md_file="$WIGGUM_HOME/lib/agents/engineering/validation-review.md"

    if [ ! -f "$md_file" ]; then
        skip_test "validation-review.md not found"
        return
    fi

    if md_agent_load "$md_file"; then
        assert_equals "engineering.validation-review" "$_MD_TYPE" "validation-review.md should have correct type"
        assert_equals "ralph_loop" "$_MD_MODE" "validation-review.md should be ralph_loop mode"
    else
        assert_failure "validation-review.md should load successfully" true
    fi
}

test_documentation_writer_md_loads() {
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local md_file="$WIGGUM_HOME/lib/agents/general/documentation-writer.md"

    if [ ! -f "$md_file" ]; then
        echo "  [SKIP] documentation-writer.md not found"
        return
    fi

    if md_agent_load "$md_file"; then
        assert_equals "general.documentation-writer" "$_MD_TYPE" "documentation-writer.md should have correct type"
        assert_equals "once" "$_MD_MODE" "documentation-writer.md should be once mode"
    else
        assert_failure "documentation-writer.md should load successfully" true
    fi
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_agent_md_sh_syntax
run_test test_parse_frontmatter_type
run_test test_parse_frontmatter_description
run_test test_parse_frontmatter_mode
run_test test_parse_frontmatter_readonly
run_test test_parse_frontmatter_required_paths
run_test test_parse_frontmatter_valid_results
run_test test_extract_system_prompt
run_test test_extract_user_prompt
run_test test_extract_continuation_prompt
run_test test_interpolate_path_variables
run_test test_interpolate_task_context
run_test test_interpolate_iteration_variables
run_test test_once_mode_detection
run_test test_resume_mode_detection
run_test test_md_agent_init_defines_functions
run_test test_agent_required_paths_returns_paths
run_test test_load_fails_on_missing_file
run_test test_load_fails_on_missing_type
run_test test_load_fails_on_missing_user_prompt
run_test test_parse_frontmatter_supervisor_interval
run_test test_supervisor_feedback_interpolation
run_test test_parse_frontmatter_plan_file
run_test test_plan_section_generation
run_test test_plan_section_empty_when_no_file
run_test test_conditional_supervisor_with_feedback
run_test test_conditional_supervisor_without_feedback
run_test test_conditional_iteration_zero
run_test test_conditional_iteration_nonzero
run_test test_conditional_file_exists
run_test test_task_executor_md_loads
run_test test_security_audit_md_loads
run_test test_validation_review_md_loads
run_test test_documentation_writer_md_loads

# Print summary
print_test_summary
exit_with_test_result
