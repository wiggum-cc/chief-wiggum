#!/usr/bin/env bash
set -euo pipefail
# Unit tests for resume-decide decision extraction pipeline
#
# Tests the three-stage extraction: XML tags → fallback keywords → backup resume
# These test the internal functions without running the full agent.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/test-framework.sh"

WIGGUM_HOME="$(cd "$SCRIPT_DIR/.." && pwd)"
export WIGGUM_HOME

# Source the stream extraction utilities
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/core/agent-stream.sh"

# Source the resume-decide agent for its internal functions
# We need to stub agent_init_metadata since we're not running the full agent
agent_init_metadata() { :; }
agent_required_paths() { :; }
agent_output_files() { :; }
agent_source_core() { :; }
agent_source_once() { :; }
agent_create_directories() { :; }
agent_setup_context() { :; }
agent_write_result() { :; }
agent_write_report() { echo "/dev/null"; }
# Stub pipeline functions
pipeline_resolve() { echo ""; }
pipeline_load() { :; }
pipeline_load_builtin_defaults() { :; }
pipeline_step_count() { echo "0"; }
pipeline_get() { echo ""; }
# Stub runtime
run_agent_once() { :; }
run_agent_resume() { :; }
epoch_now() { date +%s; }
iso_now() { date -u +"%Y-%m-%dT%H:%M:%S+0000"; }
log_section() { :; }
log_subsection() { :; }
log_kv() { :; }
source "$WIGGUM_HOME/lib/agents/system/resume-decide.sh"

setup() {
    TEST_DIR=$(mktemp -d)
}

teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# Helper: create a mock stream-JSON log file with assistant text
# =============================================================================
_create_mock_log() {
    local log_file="$1"
    local text="$2"

    # Escape text for JSON (handle newlines and quotes)
    local escaped_text
    escaped_text=$(printf '%s' "$text" | jq -Rs '.')

    echo "{\"type\":\"assistant\",\"message\":{\"content\":[{\"type\":\"text\",\"text\":${escaped_text}}]}}" > "$log_file"
}

# Create a mock log with both assistant text and result line
_create_mock_log_with_result() {
    local log_file="$1"
    local text="$2"
    local result="$3"

    local escaped_text escaped_result
    escaped_text=$(printf '%s' "$text" | jq -Rs '.')
    escaped_result=$(printf '%s' "$result" | jq -Rs '.')

    {
        echo "{\"type\":\"assistant\",\"message\":{\"content\":[{\"type\":\"text\",\"text\":${escaped_text}}]}}"
        echo "{\"type\":\"result\",\"result\":${escaped_result}}"
    } > "$log_file"
}

# =============================================================================
# Tag extraction tests (_extract_tag_content_from_stream_json)
# =============================================================================

test_tag_extraction_same_line() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log "$log_file" "Analysis done. <decision>RETRY:default:execution</decision>"

    local result
    result=$(_extract_tag_content_from_stream_json "$log_file" "decision") || true
    assert_equals "RETRY:default:execution" "$result" "Same-line decision tag"
}

test_tag_extraction_multi_line() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log "$log_file" "Analysis:
<decision>
RETRY:default:execution
</decision>
Done."

    local result
    result=$(_extract_tag_content_from_stream_json "$log_file" "decision") || true
    assert_equals "RETRY:default:execution" "$result" "Multi-line decision tag"
}

test_tag_extraction_complete() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log "$log_file" "<decision>COMPLETE</decision>"

    local result
    result=$(_extract_tag_content_from_stream_json "$log_file" "decision") || true
    assert_equals "COMPLETE" "$result" "COMPLETE decision tag"
}

test_tag_extraction_last_occurrence() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log "$log_file" "Example: <decision>ABORT</decision>
But actually: <decision>RETRY:default:execution</decision>"

    local result
    result=$(_extract_tag_content_from_stream_json "$log_file" "decision") || true
    assert_equals "RETRY:default:execution" "$result" "Should take last tag occurrence"
}

test_tag_extraction_with_surrounding_text() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log "$log_file" "My decision is: <decision>COMPLETE</decision> and that's final."

    local result
    result=$(_extract_tag_content_from_stream_json "$log_file" "decision") || true
    assert_equals "COMPLETE" "$result" "Tag with surrounding text"
}

test_tag_extraction_instructions() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log "$log_file" "<decision>COMPLETE</decision>
<instructions>All PRD items are done.</instructions>"

    local result
    result=$(_extract_tag_content_from_stream_json "$log_file" "instructions") || true
    assert_equals "All PRD items are done." "$result" "Instructions tag extraction"
}

test_tag_extraction_legacy_step() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log "$log_file" "<step>RETRY:default:execution</step>"

    local result
    result=$(_extract_tag_content_from_stream_json "$log_file" "step") || true
    assert_equals "RETRY:default:execution" "$result" "Legacy <step> tag"
}

test_tag_extraction_empty_when_missing() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log "$log_file" "No tags here, just analysis text."

    local result
    result=$(_extract_tag_content_from_stream_json "$log_file" "decision") || true
    assert_equals "" "$result" "Empty when no tag found"
}

# =============================================================================
# Fallback extraction tests (_fallback_extract_decision)
# =============================================================================

test_fallback_retry_structured() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log_with_result "$log_file" "Analysis complete" "RETRY:default:execution"

    local result
    result=$(_fallback_extract_decision "$log_file") || true
    assert_equals "RETRY:default:execution" "$result" "Structured RETRY in result text"
}

test_fallback_retry_in_assistant_text() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log "$log_file" "Based on my analysis, the decision should be RETRY:default:execution."

    local result
    result=$(_fallback_extract_decision "$log_file") || true
    assert_equals "RETRY:default:execution" "$result" "Structured RETRY in assistant text"
}

test_fallback_complete_contextual() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log_with_result "$log_file" "All done" "The decision is COMPLETE"

    local result
    result=$(_fallback_extract_decision "$log_file") || true
    assert_equals "COMPLETE" "$result" "Contextual COMPLETE keyword"
}

test_fallback_complete_recommendation() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log_with_result "$log_file" "Done" "I recommend COMPLETE based on the evidence"

    local result
    result=$(_fallback_extract_decision "$log_file") || true
    assert_equals "COMPLETE" "$result" "COMPLETE with recommend context"
}

test_fallback_complete_standalone() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log_with_result "$log_file" "Analysis" "COMPLETE"

    local result
    result=$(_fallback_extract_decision "$log_file") || true
    assert_equals "COMPLETE" "$result" "Standalone COMPLETE on own line"
}

test_fallback_complete_in_full_text() {
    local log_file="$TEST_DIR/test.log"
    # Only in assistant text, not in result
    _create_mock_log "$log_file" "My conclusion is COMPLETE. All work is done."

    local result
    result=$(_fallback_extract_decision "$log_file") || true
    assert_equals "COMPLETE" "$result" "COMPLETE found in full assistant text"
}

test_fallback_defer_contextual() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log_with_result "$log_file" "OOM" "The verdict is DEFER due to OOM"

    local result
    result=$(_fallback_extract_decision "$log_file") || true
    assert_equals "DEFER" "$result" "Contextual DEFER keyword"
}

test_fallback_defer_standalone() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log_with_result "$log_file" "Rate limited" "DEFER"

    local result
    result=$(_fallback_extract_decision "$log_file") || true
    assert_equals "DEFER" "$result" "Standalone DEFER on own line"
}

test_fallback_no_abort_from_natural_language() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log_with_result "$log_file" "Analysis" "I would abort if this fails again"

    local result
    result=$(_fallback_extract_decision "$log_file") || true
    assert_equals "" "$result" "Should NOT match ABORT from natural language"
}

test_fallback_empty_log() {
    local log_file="$TEST_DIR/test.log"
    echo "" > "$log_file"

    local result
    result=$(_fallback_extract_decision "$log_file") || true
    assert_equals "" "$result" "Empty log returns empty"
}

test_fallback_prefers_result_text_retry() {
    local log_file="$TEST_DIR/test.log"
    _create_mock_log_with_result "$log_file" \
        "RETRY:default:planning" \
        "RETRY:default:execution"

    local result
    result=$(_fallback_extract_decision "$log_file") || true
    # Result text is checked first
    assert_equals "RETRY:default:execution" "$result" "Should prefer result text RETRY"
}

# =============================================================================
# Decision parsing tests (_parse_resume_decision)
# =============================================================================

test_parse_retry_structured() {
    # shellcheck disable=SC2034
    local decision="" resume_pipeline="" resume_step_id="" reason=""
    _parse_resume_decision "RETRY:default:execution" "some instructions"

    assert_equals "RETRY" "$decision" "Decision type"
    assert_equals "default" "$resume_pipeline" "Pipeline name"
    assert_equals "execution" "$resume_step_id" "Step ID"
}

test_parse_complete() {
    # shellcheck disable=SC2034
    local decision="" resume_pipeline="" resume_step_id="" reason=""
    _parse_resume_decision "COMPLETE" "All work done"

    assert_equals "COMPLETE" "$decision" "Decision type"
    assert_equals "" "$resume_pipeline" "No pipeline for COMPLETE"
    assert_equals "" "$resume_step_id" "No step for COMPLETE"
}

test_parse_abort() {
    # shellcheck disable=SC2034
    local decision="" resume_pipeline="" resume_step_id="" reason=""
    _parse_resume_decision "ABORT" "Impossible"

    assert_equals "ABORT" "$decision" "Decision type"
}

test_parse_defer() {
    # shellcheck disable=SC2034
    local decision="" resume_pipeline="" resume_step_id="" reason=""
    _parse_resume_decision "DEFER" "OOM"

    assert_equals "DEFER" "$decision" "Decision type"
}

test_parse_legacy_bare_step() {
    # shellcheck disable=SC2034
    local decision="" resume_pipeline="" resume_step_id="" reason=""
    _parse_resume_decision "execution" ""

    assert_equals "RETRY" "$decision" "Bare step treated as RETRY"
    assert_equals "execution" "$resume_step_id" "Step ID from bare format"
}

# =============================================================================
# Run tests
# =============================================================================
run_test test_tag_extraction_same_line
run_test test_tag_extraction_multi_line
run_test test_tag_extraction_complete
run_test test_tag_extraction_last_occurrence
run_test test_tag_extraction_with_surrounding_text
run_test test_tag_extraction_instructions
run_test test_tag_extraction_legacy_step
run_test test_tag_extraction_empty_when_missing
run_test test_fallback_retry_structured
run_test test_fallback_retry_in_assistant_text
run_test test_fallback_complete_contextual
run_test test_fallback_complete_recommendation
run_test test_fallback_complete_standalone
run_test test_fallback_complete_in_full_text
run_test test_fallback_defer_contextual
run_test test_fallback_defer_standalone
run_test test_fallback_no_abort_from_natural_language
run_test test_fallback_empty_log
run_test test_fallback_prefers_result_text_retry
run_test test_parse_retry_structured
run_test test_parse_complete
run_test test_parse_abort
run_test test_parse_defer
run_test test_parse_legacy_bare_step

print_test_summary
exit_with_test_result
