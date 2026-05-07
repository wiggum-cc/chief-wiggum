#!/usr/bin/env bash
# pr-merge-optimizer.sh - Optimized PR merge strategy for multiple conflicting PRs
#
# This module implements a global optimization approach to merging multiple PRs:
#
# 1. GATHER: Collect data on all pending PRs (files modified, merge status)
# 2. ANALYZE: Build conflict graph showing which PRs conflict with each other
# 3. OPTIMIZE: Find optimal merge order to maximize successful merges
# 4. EXECUTE: Merge in order with re-evaluation after each merge
# 5. RESOLVE: Handle remaining conflicts (single-PR vs multi-PR)
#
# Data file: .ralph/pr-merge-state.json
# Format:
# {
#   "prs": {
#     "TASK-001": {
#       "pr_number": 20,
#       "worker_dir": "/path/to/worker",
#       "branch": "task-001-feature",
#       "files_modified": ["src/api.ts", "src/utils.ts"],
#       "base_commit": "abc123",
#       "has_new_comments": false,
#       "copilot_reviewed": true,
#       "mergeable_to_main": true,
#       "conflict_files_with_main": []
#     }
#   },
#   "conflict_graph": {
#     "TASK-001": ["TASK-002", "TASK-003"],
#     "TASK-002": ["TASK-001"],
#     "TASK-003": ["TASK-001"]
#   },
#   "merge_order": ["TASK-004", "TASK-005", "TASK-002", ...],
#   "last_updated": "2024-01-27T12:00:00Z"
# }
#
# This file is a facade that sources the split modules for maintainability:
#   - pr-merge-data.sh    - Data gathering (Phase 1: GATHER)
#   - pr-merge-graph.sh   - Conflict graph and optimization (Phase 2-3)
#   - pr-merge-executor.sh - Merge execution and orchestration (Phase 4-5)

set -euo pipefail

[ -n "${_PR_MERGE_OPTIMIZER_LOADED:-}" ] && return 0
_PR_MERGE_OPTIMIZER_LOADED=1

# Source dependencies
[ -z "${_WIGGUM_SRC_LOGGER_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/logger.sh"
[ -z "${_WIGGUM_SRC_FILE_LOCK_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/scheduler/conflict-queue.sh"
source "$WIGGUM_HOME/lib/scheduler/conflict-registry.sh"
source "$WIGGUM_HOME/lib/scheduler/batch-coordination.sh"
source "$WIGGUM_HOME/lib/tasks/task-parser.sh"

# State file path
_pr_merge_state_file() {
    echo "$1/orchestrator/pr-merge-state.json"
}

# Initialize or reset the PR merge state
#
# Args:
#   ralph_dir - Ralph directory path
pr_merge_init() {
    local ralph_dir="$1"
    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    jq -n '{
        prs: {},
        conflict_graph: {},
        merge_order: [],
        merged_this_cycle: [],
        last_updated: now | strftime("%Y-%m-%dT%H:%M:%SZ")
    }' > "$state_file"
}

# Source the split modules
# Order matters: data -> graph -> executor (executor depends on functions from data and graph)
source "$WIGGUM_HOME/lib/scheduler/pr-merge-data.sh"
source "$WIGGUM_HOME/lib/scheduler/pr-merge-graph.sh"
source "$WIGGUM_HOME/lib/scheduler/pr-merge-executor.sh"
