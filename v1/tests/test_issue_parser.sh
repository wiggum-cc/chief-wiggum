#!/usr/bin/env bash
set -euo pipefail
# Test GitHub issue parser (lib/github/issue-parser.sh)

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/github/issue-parser.sh"

# =============================================================================
# Task ID Parsing
# =============================================================================

test_parse_task_id_basic() {
    local result
    result=$(github_issue_parse_task_id "[GH-42] Add dark mode")
    assert_equals "GH-42" "$result" "Should extract GH-42 from title"
}

test_parse_task_id_bold() {
    local result
    result=$(github_issue_parse_task_id "**[FEAT-7]** Implement OAuth login")
    assert_equals "FEAT-7" "$result" "Should extract FEAT-7 from bold brackets"
}

test_parse_task_id_long_prefix() {
    local result
    result=$(github_issue_parse_task_id "[PIPELINE-1234] Complex task")
    assert_equals "PIPELINE-1234" "$result" "Should handle long prefix with 4-digit number"
}

test_parse_task_id_short_prefix() {
    local result
    result=$(github_issue_parse_task_id "[BG-1] Quick fix")
    assert_equals "BG-1" "$result" "Should handle 2-letter prefix with 1-digit number"
}

test_parse_task_id_missing() {
    local result
    result=$(github_issue_parse_task_id "No task ID here")
    assert_equals "" "$result" "Should return empty for missing task ID"
}

test_parse_task_id_invalid_prefix() {
    local result
    result=$(github_issue_parse_task_id "[A-42] Too short prefix")
    assert_equals "" "$result" "Should reject single-letter prefix"
}

test_parse_task_id_invalid_number() {
    local result
    result=$(github_issue_parse_task_id "[GH-12345] Too many digits")
    assert_equals "" "$result" "Should reject 5-digit number"
}

# =============================================================================
# Brief Description Parsing
# =============================================================================

test_parse_brief_basic() {
    local result
    result=$(github_issue_parse_brief "[GH-42] Add dark mode support")
    assert_equals "Add dark mode support" "$result" "Should extract brief from plain brackets"
}

test_parse_brief_bold() {
    local result
    result=$(github_issue_parse_brief "**[FEAT-7]** Implement OAuth login")
    assert_equals "Implement OAuth login" "$result" "Should extract brief from bold brackets"
}

# =============================================================================
# Body Parsing
# =============================================================================

test_parse_body_inline_fields() {
    local body="Some description text.

Priority: HIGH
Complexity: MEDIUM
Dependencies: GH-10, GH-15"

    local result
    result=$(github_issue_parse_body_json "$body")

    local priority complexity dependencies description
    priority=$(echo "$result" | jq -r '.priority')
    complexity=$(echo "$result" | jq -r '.complexity')
    dependencies=$(echo "$result" | jq -r '.dependencies')
    description=$(echo "$result" | jq -r '.description')

    assert_equals "HIGH" "$priority" "Should extract priority"
    assert_equals "MEDIUM" "$complexity" "Should extract complexity"
    assert_equals "GH-10, GH-15" "$dependencies" "Should extract dependencies"
    assert_equals "Some description text." "$description" "Should extract description"
}

test_parse_body_sections() {
    local body="Main description.

## Scope
- Feature A
- Feature B

## Out of Scope
- Feature C

## Acceptance Criteria
- Must pass tests
- Must handle edge cases"

    local result
    result=$(github_issue_parse_body_json "$body")

    local scope out_of_scope acceptance_criteria
    scope=$(echo "$result" | jq -r '.scope')
    out_of_scope=$(echo "$result" | jq -r '.out_of_scope')
    acceptance_criteria=$(echo "$result" | jq -r '.acceptance_criteria')

    assert_output_contains "$scope" "Feature A" "Scope should contain Feature A"
    assert_output_contains "$scope" "Feature B" "Scope should contain Feature B"
    assert_output_contains "$out_of_scope" "Feature C" "Out of Scope should contain Feature C"
    assert_output_contains "$acceptance_criteria" "Must pass tests" "AC should contain tests requirement"
}

test_parse_body_empty() {
    local result
    result=$(github_issue_parse_body_json "")

    local description priority
    description=$(echo "$result" | jq -r '.description')
    priority=$(echo "$result" | jq -r '.priority')

    assert_equals "" "$description" "Empty body should give empty description"
    assert_equals "" "$priority" "Empty body should give empty priority"
}

test_parse_body_no_inline_fields() {
    local body="Just a plain description.
With multiple lines.
No structured fields."

    local result
    result=$(github_issue_parse_body_json "$body")

    local description priority
    description=$(echo "$result" | jq -r '.description')
    priority=$(echo "$result" | jq -r '.priority')

    assert_output_contains "$description" "Just a plain description." "Should capture full description"
    assert_equals "" "$priority" "Should have empty priority"
}

test_parse_body_dependencies_none() {
    local body="Description.
Dependencies: none"

    local result
    result=$(github_issue_parse_body_json "$body")

    local dependencies
    dependencies=$(echo "$result" | jq -r '.dependencies')
    assert_equals "none" "$dependencies" "Should capture 'none' dependencies"
}

test_parse_body_case_insensitive() {
    local body="priority: low
complexity: high
dependencies: GH-1"

    local result
    result=$(github_issue_parse_body_json "$body")

    local priority complexity
    priority=$(echo "$result" | jq -r '.priority')
    complexity=$(echo "$result" | jq -r '.complexity')

    assert_equals "LOW" "$priority" "Should handle lowercase priority"
    assert_equals "HIGH" "$complexity" "Should handle lowercase complexity"
}

# =============================================================================
# Dependency Validation
# =============================================================================

test_validate_deps_valid() {
    local result
    result=$(github_issue_validate_deps "GH-10, FEAT-7, BUG-123")
    assert_equals "GH-10, FEAT-7, BUG-123" "$result" "Should keep valid deps"
}

test_validate_deps_mixed() {
    local result
    result=$(github_issue_validate_deps "GH-10, invalid, FEAT-7")
    assert_equals "GH-10, FEAT-7" "$result" "Should filter out invalid deps"
}

test_validate_deps_none() {
    local result
    result=$(github_issue_validate_deps "none")
    assert_equals "none" "$result" "Should pass through 'none'"
}

test_validate_deps_empty() {
    local result
    result=$(github_issue_validate_deps "")
    assert_equals "none" "$result" "Should return 'none' for empty"
}

test_validate_deps_all_invalid() {
    local result
    result=$(github_issue_validate_deps "abc, 123, x-y")
    assert_equals "none" "$result" "Should return 'none' when all invalid"
}

# =============================================================================
# Full Issue Parsing
# =============================================================================

test_parse_full_issue() {
    local issue_json='{"number":42,"title":"[GH-42] Add dark mode","body":"Support dark/light toggling.\n\nPriority: HIGH\nDependencies: GH-30","labels":[{"name":"wiggum"},{"name":"priority:high"}],"author":{"login":"testuser","id":"12345"},"state":"OPEN","updatedAt":"2025-01-23T12:00:00Z"}'

    local result
    result=$(github_issue_parse "$issue_json")

    local task_id brief number
    task_id=$(echo "$result" | jq -r '.task_id')
    brief=$(echo "$result" | jq -r '.brief')
    number=$(echo "$result" | jq -r '.number')

    assert_equals "GH-42" "$task_id" "Should parse task ID"
    assert_equals "Add dark mode" "$brief" "Should parse brief"
    assert_equals "42" "$number" "Should parse number"
}

test_parse_full_issue_no_task_id() {
    local issue_json='{"number":99,"title":"No task ID here","body":"Some body","labels":[],"author":{"login":"testuser","id":"12345"},"state":"OPEN","updatedAt":"2025-01-23T12:00:00Z"}'

    local result exit_code=0
    result=$(github_issue_parse "$issue_json") || exit_code=$?

    assert_equals "1" "$exit_code" "Should return 1 for missing task ID"
}

# =============================================================================
# Heading-Based Format (round-trip with extract_task output)
# =============================================================================

test_parse_body_heading_fields() {
    # This is the format extract_task produces for issue bodies
    local body="# Task: OPT-004 - Backend performance optimizations

## Description
Implement N+1 upsert fix, batch graph mutations, and reduce RwLock contention.

## Priority
MEDIUM

## Dependencies
OPT-001, OPT-002

## Scope
- Fix N+1 upsert pattern
- Implement batch mutation API

## Checklist
- [ ] Fix upsert
- [ ] Mark this PRD as complete"

    local result
    result=$(github_issue_parse_body_json "$body")

    local description priority dependencies scope
    description=$(echo "$result" | jq -r '.description')
    priority=$(echo "$result" | jq -r '.priority')
    dependencies=$(echo "$result" | jq -r '.dependencies')
    scope=$(echo "$result" | jq -r '.scope')

    assert_equals "MEDIUM" "$priority" "Should extract priority from ## heading"
    assert_equals "OPT-001, OPT-002" "$dependencies" "Should extract dependencies from ## heading"
    assert_output_contains "$description" "Implement N+1 upsert fix" "Description should have body text"
    assert_output_not_contains "$description" "## Priority" "Description should NOT contain ## Priority heading"
    assert_output_not_contains "$description" "## Dependencies" "Description should NOT contain ## Dependencies heading"
    assert_output_not_contains "$description" "# Task:" "Description should NOT contain title heading"
    assert_output_contains "$scope" "Fix N+1 upsert pattern" "Should extract scope"
}

test_parse_body_heading_complexity() {
    local body="## Description
Some task.

## Complexity
HIGH

## Priority
LOW"

    local result
    result=$(github_issue_parse_body_json "$body")

    local priority complexity
    priority=$(echo "$result" | jq -r '.priority')
    complexity=$(echo "$result" | jq -r '.complexity')

    assert_equals "LOW" "$priority" "Should extract priority from heading"
    assert_equals "HIGH" "$complexity" "Should extract complexity from heading"
}

test_parse_body_mixed_inline_and_heading() {
    # Inline fields should still work alongside headings
    local body="Priority: HIGH

## Description
Some description text.

## Scope
- Item one"

    local result
    result=$(github_issue_parse_body_json "$body")

    local priority description scope
    priority=$(echo "$result" | jq -r '.priority')
    description=$(echo "$result" | jq -r '.description')
    scope=$(echo "$result" | jq -r '.scope')

    assert_equals "HIGH" "$priority" "Inline priority should take precedence"
    assert_output_contains "$description" "Some description text." "Should extract description"
    assert_output_contains "$scope" "Item one" "Should extract scope"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_parse_task_id_basic
run_test test_parse_task_id_bold
run_test test_parse_task_id_long_prefix
run_test test_parse_task_id_short_prefix
run_test test_parse_task_id_missing
run_test test_parse_task_id_invalid_prefix
run_test test_parse_task_id_invalid_number
run_test test_parse_brief_basic
run_test test_parse_brief_bold
run_test test_parse_body_inline_fields
run_test test_parse_body_sections
run_test test_parse_body_empty
run_test test_parse_body_no_inline_fields
run_test test_parse_body_dependencies_none
run_test test_parse_body_case_insensitive
run_test test_validate_deps_valid
run_test test_validate_deps_mixed
run_test test_validate_deps_none
run_test test_validate_deps_empty
run_test test_validate_deps_all_invalid
run_test test_parse_full_issue
run_test test_parse_full_issue_no_task_id
run_test test_parse_body_heading_fields
run_test test_parse_body_heading_complexity
run_test test_parse_body_mixed_inline_and_heading

print_test_summary
exit_with_test_result
