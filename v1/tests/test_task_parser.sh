#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/tasks/task-parser.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/tasks/task-parser.sh"

# =============================================================================
# has_incomplete_tasks() Tests
# =============================================================================

test_has_incomplete_tasks_returns_true_when_pending() {
    local result
    has_incomplete_tasks "$FIXTURES_DIR/kanban-with-deps.md"
    result=$?
    assert_equals "0" "$result" "Should return 0 (true) when pending tasks exist"
}

test_has_incomplete_tasks_returns_false_when_all_complete() {
    local result
    has_incomplete_tasks "$FIXTURES_DIR/kanban-all-complete.md"
    result=$?
    assert_equals "1" "$result" "Should return 1 (false) when all tasks complete"
}

# =============================================================================
# get_prd_status() Tests
# =============================================================================

test_get_prd_status_incomplete() {
    local status
    status=$(get_prd_status "$FIXTURES_DIR/kanban-with-deps.md")
    assert_equals "INCOMPLETE" "$status" "Should return INCOMPLETE when pending tasks exist"
}

test_get_prd_status_complete() {
    local status
    status=$(get_prd_status "$FIXTURES_DIR/kanban-all-complete.md")
    assert_equals "COMPLETE" "$status" "Should return COMPLETE when all tasks done"
}

test_get_prd_status_failed() {
    local status
    status=$(get_prd_status "$FIXTURES_DIR/kanban-with-failed.md")
    assert_equals "FAILED" "$status" "Should return FAILED when any task has [*] status"
}

# =============================================================================
# get_todo_tasks() Tests
# =============================================================================

test_get_todo_tasks_extracts_pending_only() {
    local tasks
    tasks=$(get_todo_tasks "$FIXTURES_DIR/kanban-with-deps.md")

    assert_output_contains "$tasks" "TASK-002" "Should include pending TASK-002"
    assert_output_contains "$tasks" "TASK-003" "Should include pending TASK-003"
    assert_output_contains "$tasks" "TASK-004" "Should include pending TASK-004"

    # Should NOT include completed or in-progress tasks
    if echo "$tasks" | grep -q "TASK-001"; then
        echo -e "  ${RED}X${NC} Should NOT include completed TASK-001"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Correctly excludes completed TASK-001"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if echo "$tasks" | grep -q "TASK-005"; then
        echo -e "  ${RED}X${NC} Should NOT include in-progress TASK-005"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Correctly excludes in-progress TASK-005"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_get_todo_tasks_empty_when_all_complete() {
    local tasks
    tasks=$(get_todo_tasks "$FIXTURES_DIR/kanban-all-complete.md")
    assert_equals "" "$tasks" "Should return empty when no pending tasks"
}

# =============================================================================
# get_failed_tasks() Tests
# =============================================================================

test_get_failed_tasks_extracts_failed_only() {
    local tasks
    tasks=$(get_failed_tasks "$FIXTURES_DIR/kanban-with-failed.md")
    assert_output_contains "$tasks" "TASK-002" "Should include failed TASK-002"

    local count
    count=$(echo "$tasks" | grep -c "TASK") || count=0
    assert_equals "1" "$count" "Should only return one failed task"
}

test_get_failed_tasks_empty_when_none_failed() {
    local tasks
    tasks=$(get_failed_tasks "$FIXTURES_DIR/kanban-all-complete.md")
    assert_equals "" "$tasks" "Should return empty when no failed tasks"
}

# =============================================================================
# get_all_tasks_with_metadata() Tests
# =============================================================================

test_get_all_tasks_with_metadata_format() {
    local metadata
    metadata=$(get_all_tasks_with_metadata "$FIXTURES_DIR/kanban-with-deps.md")

    # Check format: task_id|status|priority|dependencies
    assert_output_contains "$metadata" "TASK-001|x|HIGH|" "Should include completed task with metadata"
    assert_output_contains "$metadata" "TASK-002| |MEDIUM|TASK-001" "Should include pending task with deps"
}

test_get_all_tasks_with_metadata_multiple_deps() {
    local metadata
    metadata=$(get_all_tasks_with_metadata "$FIXTURES_DIR/kanban-with-deps.md")

    # TASK-004 has multiple dependencies
    assert_output_contains "$metadata" "TASK-004| |LOW|TASK-001, TASK-002" "Should parse multiple dependencies"
}

# =============================================================================
# get_task_dependencies() Tests
# =============================================================================

test_get_task_dependencies_single() {
    local deps
    deps=$(get_task_dependencies "$FIXTURES_DIR/kanban-with-deps.md" "TASK-002")
    assert_equals "TASK-001" "$deps" "Should return single dependency"
}

test_get_task_dependencies_multiple() {
    local deps
    deps=$(get_task_dependencies "$FIXTURES_DIR/kanban-with-deps.md" "TASK-004")
    assert_output_contains "$deps" "TASK-001" "Should include first dependency"
    assert_output_contains "$deps" "TASK-002" "Should include second dependency"
}

test_get_task_dependencies_none() {
    local deps
    deps=$(get_task_dependencies "$FIXTURES_DIR/kanban-with-deps.md" "TASK-001")
    assert_equals "" "$deps" "Should return empty for task with no deps"
}

# =============================================================================
# get_task_priority() Tests
# =============================================================================

test_get_task_priority_high() {
    local priority
    priority=$(get_task_priority "$FIXTURES_DIR/kanban-priorities.md" "TASK-002")
    assert_equals "HIGH" "$priority" "Should return HIGH priority"
}

test_get_task_priority_medium() {
    local priority
    priority=$(get_task_priority "$FIXTURES_DIR/kanban-priorities.md" "TASK-003")
    assert_equals "MEDIUM" "$priority" "Should return MEDIUM priority"
}

test_get_task_priority_low() {
    local priority
    priority=$(get_task_priority "$FIXTURES_DIR/kanban-priorities.md" "TASK-001")
    assert_equals "LOW" "$priority" "Should return LOW priority"
}

# =============================================================================
# get_task_status() Tests
# =============================================================================

test_get_task_status_pending() {
    local status
    status=$(get_task_status "$FIXTURES_DIR/kanban-with-deps.md" "TASK-002")
    assert_equals " " "$status" "Should return space for pending task"
}

test_get_task_status_complete() {
    local status
    status=$(get_task_status "$FIXTURES_DIR/kanban-with-deps.md" "TASK-001")
    assert_equals "x" "$status" "Should return x for completed task"
}

test_get_task_status_in_progress() {
    local status
    status=$(get_task_status "$FIXTURES_DIR/kanban-with-deps.md" "TASK-005")
    assert_equals "=" "$status" "Should return = for in-progress task"
}

test_get_task_status_failed() {
    local status
    status=$(get_task_status "$FIXTURES_DIR/kanban-with-failed.md" "TASK-002")
    assert_equals "*" "$status" "Should return * for failed task"
}

# =============================================================================
# are_dependencies_satisfied() Tests
# =============================================================================

test_are_dependencies_satisfied_no_deps() {
    are_dependencies_satisfied "$FIXTURES_DIR/kanban-with-deps.md" "TASK-001"
    local result=$?
    assert_equals "0" "$result" "Task with no deps should be satisfied"
}

test_are_dependencies_satisfied_deps_complete() {
    are_dependencies_satisfied "$FIXTURES_DIR/kanban-with-deps.md" "TASK-002"
    local result=$?
    assert_equals "0" "$result" "Task whose deps are complete should be satisfied"
}

test_are_dependencies_satisfied_deps_incomplete() {
    are_dependencies_satisfied "$FIXTURES_DIR/kanban-with-deps.md" "TASK-003"
    local result=$?
    assert_equals "1" "$result" "Task with incomplete deps should not be satisfied"
}

test_are_dependencies_satisfied_multiple_deps_partial() {
    are_dependencies_satisfied "$FIXTURES_DIR/kanban-with-deps.md" "TASK-004"
    local result=$?
    assert_equals "1" "$result" "Task with partially complete deps should not be satisfied"
}

# =============================================================================
# get_ready_tasks() Tests
# =============================================================================

test_get_ready_tasks_filters_blocked() {
    local ready
    ready=$(get_ready_tasks "$FIXTURES_DIR/kanban-with-deps.md")

    # TASK-002 should be ready (dep TASK-001 is complete)
    assert_output_contains "$ready" "TASK-002" "TASK-002 should be ready"

    # TASK-003 should NOT be ready (dep TASK-002 is not complete)
    if echo "$ready" | grep -q "TASK-003"; then
        echo -e "  ${RED}X${NC} TASK-003 should be blocked"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} TASK-003 correctly blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_get_ready_tasks_sorted_by_priority() {
    local ready
    ready=$(get_ready_tasks "$FIXTURES_DIR/kanban-priorities.md")

    # Convert to array and check order
    local second_task
    second_task=$(echo "$ready" | sed -n '2p')

    # HIGH priority tasks should come after CRITICAL (TASK-002 or TASK-004)
    if [[ "$second_task" == "TASK-002" || "$second_task" == "TASK-004" ]]; then
        echo -e "  ${GREEN}✓${NC} High priority task returned after CRITICAL"
    else
        echo -e "  ${RED}X${NC} Expected HIGH priority task second, got $second_task"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    # LOW priority task should be last
    local last_task
    last_task=$(echo "$ready" | tail -1)
    assert_equals "TASK-001" "$last_task" "LOW priority task should be last"
}

test_get_ready_tasks_critical_priority_first() {
    local ready
    ready=$(get_ready_tasks "$FIXTURES_DIR/kanban-priorities.md")

    # CRITICAL priority task should come first
    local first_task
    first_task=$(echo "$ready" | head -1)
    assert_equals "TASK-005" "$first_task" "CRITICAL priority task should be first"
}

test_get_ready_tasks_sibling_wip_penalty() {
    local ready
    ready=$(get_ready_tasks "$FIXTURES_DIR/kanban-sibling-wip.md")

    # OTHER-001 (HIGH, no penalty) should come first
    local first_task
    first_task=$(echo "$ready" | head -1)
    assert_equals "OTHER-001" "$first_task" "Unpenalized HIGH task should be first"

    # OTHER-002 (MEDIUM, no penalty) should come second
    local second_task
    second_task=$(echo "$ready" | sed -n '2p')
    assert_equals "OTHER-002" "$second_task" "Unpenalized MEDIUM task should be second"

    # All penalized tasks (FEAT-002, BUG-002, REFAC-002) should come last
    # They are HIGH priority but penalized by +2, making them LOW-equivalent (3)
    local last_three
    last_three=$(echo "$ready" | tail -3 | sort)
    local expected_penalized
    expected_penalized=$(echo -e "BUG-002\nFEAT-002\nREFAC-002")
    assert_equals "$expected_penalized" "$last_three" "All penalized siblings should be last"
}

test_get_ready_tasks_plan_bonus() {
    local ralph_dir="$FIXTURES_DIR/ralph-plans"
    local kanban="$ralph_dir/kanban.md"

    # Pass ralph_dir to enable plan bonus
    local ready
    ready=$(get_ready_tasks "$kanban" "" 10 20000 "$ralph_dir" 5000)

    # TASK-002 (HIGH with plan, 10000-5000=5000) should come before TASK-001 (HIGH without plan, 10000)
    local first_task
    first_task=$(echo "$ready" | head -1)
    assert_equals "TASK-002" "$first_task" "HIGH task with plan should be first"

    # TASK-001 (HIGH without plan) should come second
    local second_task
    second_task=$(echo "$ready" | sed -n '2p')
    assert_equals "TASK-001" "$second_task" "HIGH task without plan should be second"

    # TASK-003 (MEDIUM without plan) should be last
    local last_task
    last_task=$(echo "$ready" | tail -1)
    assert_equals "TASK-003" "$last_task" "MEDIUM task without plan should be last"
}

# =============================================================================
# get_blocked_tasks() Tests
# =============================================================================

test_get_blocked_tasks_identifies_blocked() {
    local blocked
    blocked=$(get_blocked_tasks "$FIXTURES_DIR/kanban-with-deps.md")

    # TASK-003 should be blocked (depends on incomplete TASK-002)
    assert_output_contains "$blocked" "TASK-003" "TASK-003 should be blocked"

    # TASK-004 should be blocked (depends on incomplete TASK-002)
    assert_output_contains "$blocked" "TASK-004" "TASK-004 should be blocked"

    # TASK-002 should NOT be blocked (its dep TASK-001 is complete)
    if echo "$blocked" | grep -q "TASK-002"; then
        echo -e "  ${RED}X${NC} TASK-002 should not be blocked"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} TASK-002 correctly not blocked"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# get_unsatisfied_dependencies() Tests
# =============================================================================

test_get_unsatisfied_dependencies_returns_incomplete() {
    local unsatisfied
    unsatisfied=$(get_unsatisfied_dependencies "$FIXTURES_DIR/kanban-with-deps.md" "TASK-003")
    assert_equals "TASK-002" "$unsatisfied" "Should return incomplete dependency"
}

test_get_unsatisfied_dependencies_empty_when_satisfied() {
    local unsatisfied
    unsatisfied=$(get_unsatisfied_dependencies "$FIXTURES_DIR/kanban-with-deps.md" "TASK-002")
    assert_equals "" "$unsatisfied" "Should return empty when deps satisfied"
}

# =============================================================================
# detect_circular_dependencies() Tests
# =============================================================================

test_detect_circular_dependencies_finds_cycle() {
    local output
    output=$(detect_circular_dependencies "$FIXTURES_DIR/kanban-circular-deps.md" 2>&1)
    local result=$?

    assert_equals "1" "$result" "Should return 1 when cycle detected"
    assert_output_contains "$output" "CYCLE:" "Should report cycle with CYCLE: prefix"
    assert_output_contains "$output" "TASK-001" "Should include TASK-001 in cycle"
    assert_output_contains "$output" "TASK-002" "Should include TASK-002 in cycle"
    assert_output_contains "$output" "TASK-003" "Should include TASK-003 in cycle"
}

test_detect_circular_dependencies_no_cycle() {
    local result
    detect_circular_dependencies "$FIXTURES_DIR/kanban-with-deps.md" > /dev/null 2>&1
    result=$?
    assert_equals "0" "$result" "Should return 0 when no cycle"
}

test_detect_circular_dependencies_finds_self_dependency() {
    local output
    output=$(detect_circular_dependencies "$FIXTURES_DIR/kanban-self-dep.md" 2>&1)
    local result=$?

    assert_equals "1" "$result" "Should return 1 when self-dependency detected"
    assert_output_contains "$output" "SELF:TASK-002" "Should report self-dependency with SELF: prefix"
}

test_detect_circular_dependencies_self_dep_not_in_cycle_output() {
    local output
    output=$(detect_circular_dependencies "$FIXTURES_DIR/kanban-self-dep.md" 2>&1)

    # Self-dependency should only appear in SELF: line, not CYCLE:
    if echo "$output" | grep -q "^CYCLE:"; then
        echo -e "  ${RED}X${NC} Self-dependency should not produce CYCLE: line"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Self-dependency correctly not in CYCLE: output"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# extract_task() Tests
# =============================================================================

test_extract_task_includes_title() {
    local prd
    prd=$(extract_task "TASK-002" "$FIXTURES_DIR/kanban-with-deps.md")
    assert_output_contains "$prd" "Task: TASK-002" "Should include task ID in title"
}

test_extract_task_includes_description() {
    local prd
    prd=$(extract_task "TASK-002" "$FIXTURES_DIR/kanban-with-deps.md")
    assert_output_contains "$prd" "Description" "Should include Description section"
}

test_extract_task_includes_checklist() {
    local prd
    prd=$(extract_task "TASK-002" "$FIXTURES_DIR/kanban-with-deps.md")
    assert_output_contains "$prd" "## Checklist" "Should include Checklist section"
}

# =============================================================================
# Run All Tests
# =============================================================================

# has_incomplete_tasks tests
run_test test_has_incomplete_tasks_returns_true_when_pending
run_test test_has_incomplete_tasks_returns_false_when_all_complete

# get_prd_status tests
run_test test_get_prd_status_incomplete
run_test test_get_prd_status_complete
run_test test_get_prd_status_failed

# get_todo_tasks tests
run_test test_get_todo_tasks_extracts_pending_only
run_test test_get_todo_tasks_empty_when_all_complete

# get_failed_tasks tests
run_test test_get_failed_tasks_extracts_failed_only
run_test test_get_failed_tasks_empty_when_none_failed

# get_all_tasks_with_metadata tests
run_test test_get_all_tasks_with_metadata_format
run_test test_get_all_tasks_with_metadata_multiple_deps

# get_task_dependencies tests
run_test test_get_task_dependencies_single
run_test test_get_task_dependencies_multiple
run_test test_get_task_dependencies_none

# get_task_priority tests
run_test test_get_task_priority_high
run_test test_get_task_priority_medium
run_test test_get_task_priority_low

# get_task_status tests
run_test test_get_task_status_pending
run_test test_get_task_status_complete
run_test test_get_task_status_in_progress
run_test test_get_task_status_failed

# are_dependencies_satisfied tests
run_test test_are_dependencies_satisfied_no_deps
run_test test_are_dependencies_satisfied_deps_complete
run_test test_are_dependencies_satisfied_deps_incomplete
run_test test_are_dependencies_satisfied_multiple_deps_partial

# get_ready_tasks tests
run_test test_get_ready_tasks_filters_blocked
run_test test_get_ready_tasks_sorted_by_priority
run_test test_get_ready_tasks_critical_priority_first
run_test test_get_ready_tasks_sibling_wip_penalty
run_test test_get_ready_tasks_plan_bonus

# get_blocked_tasks tests
run_test test_get_blocked_tasks_identifies_blocked

# get_unsatisfied_dependencies tests
run_test test_get_unsatisfied_dependencies_returns_incomplete
run_test test_get_unsatisfied_dependencies_empty_when_satisfied

# detect_circular_dependencies tests
run_test test_detect_circular_dependencies_finds_cycle
run_test test_detect_circular_dependencies_no_cycle
run_test test_detect_circular_dependencies_finds_self_dependency
run_test test_detect_circular_dependencies_self_dep_not_in_cycle_output

# extract_task tests
run_test test_extract_task_includes_title
run_test test_extract_task_includes_description
run_test test_extract_task_includes_checklist

print_test_summary
exit_with_test_result
