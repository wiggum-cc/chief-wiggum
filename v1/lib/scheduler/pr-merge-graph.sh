#!/usr/bin/env bash
# pr-merge-graph.sh - Conflict graph building and optimization for PR merges
#
# Provides:
#   - Phase 2: ANALYZE - Build conflict graph from PR data
#   - Phase 3: OPTIMIZE - Maximum Independent Set algorithm for optimal merge order
#
# Split from pr-merge-optimizer.sh for maintainability.
set -euo pipefail

[ -n "${_PR_MERGE_GRAPH_LOADED:-}" ] && return 0
_PR_MERGE_GRAPH_LOADED=1

# =============================================================================
# PHASE 2: ANALYZE - Build conflict graph
# =============================================================================

# Check if two PRs have file-level conflicts (overlapping modified files)
#
# Args:
#   files_a - JSON array of files from PR A
#   files_b - JSON array of files from PR B
#
# Returns: 0 if overlap exists, 1 otherwise
# Outputs: JSON array of overlapping files
_check_file_overlap() {
    local files_a="$1"
    local files_b="$2"

    local overlap
    overlap=$(jq -n --argjson a "$files_a" --argjson b "$files_b" \
        '($a + $b) | group_by(.) | map(select(length > 1) | .[0])')

    local count
    count=$(echo "$overlap" | jq 'length')
    count="${count:-0}"

    echo "$overlap"
    [ "$count" -gt 0 ]
}

# Build the conflict graph from gathered PR data
#
# The conflict graph shows which PRs conflict with each other based on:
# 1. File-level overlap (same files modified)
# 2. Actual merge conflicts (if we have that data)
#
# Args:
#   ralph_dir - Ralph directory path
pr_merge_build_conflict_graph() {
    local ralph_dir="$1"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    log_debug "Phase 2: Building conflict graph..."

    # Get all task IDs
    local task_ids
    task_ids=$(jq -r '.prs | keys[]' "$state_file")

    # Initialize empty conflict graph
    jq '.conflict_graph = {}' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    # For each pair of PRs, check for conflicts
    local task_array=()
    while IFS= read -r task_id; do
        [ -n "$task_id" ] && task_array+=("$task_id")
    done <<< "$task_ids"

    local conflict_count=0
    local i j
    for ((i=0; i<${#task_array[@]}; i++)); do
        local task_a="${task_array[$i]}"
        local files_a
        files_a=$(jq -r --arg t "$task_a" '.prs[$t].files_modified' "$state_file")

        for ((j=i+1; j<${#task_array[@]}; j++)); do
            local task_b="${task_array[$j]}"
            local files_b
            files_b=$(jq -r --arg t "$task_b" '.prs[$t].files_modified' "$state_file")

            # Check for overlap
            local overlap
            if overlap=$(_check_file_overlap "$files_a" "$files_b"); then
                log "  Conflict: $task_a ↔ $task_b (files: $(echo "$overlap" | jq -r 'join(", ")'))"

                # Add to both sides of the graph
                jq --arg a "$task_a" --arg b "$task_b" '
                    .conflict_graph[$a] = ((.conflict_graph[$a] // []) + [$b] | unique) |
                    .conflict_graph[$b] = ((.conflict_graph[$b] // []) + [$a] | unique)
                ' "$state_file" > "$state_file.tmp"
                mv "$state_file.tmp" "$state_file"

                ((++conflict_count))
            fi
        done
    done

    log "  Found $conflict_count conflict pair(s)"

    # Identify PRs with no conflicts (independent)
    local independent_count=0
    for task_id in "${task_array[@]}"; do
        local conflicts
        conflicts=$(jq -r --arg t "$task_id" '.conflict_graph[$t] // [] | length' "$state_file")
        if [ "$conflicts" -eq 0 ]; then
            ((++independent_count))
        fi
    done

    log "  Independent PRs (no conflicts): $independent_count"
}

# =============================================================================
# PHASE 3: OPTIMIZE - Find optimal merge order using Dynamic Programming
# =============================================================================
#
# This is the Maximum Independent Set (MIS) problem on the conflict graph.
# We want to find the largest set of PRs that can be merged without conflicts.
#
# Algorithm: Bitmask DP for exact solution (feasible for n < 20 PRs)
# - State: dp[mask] = 1 if subset represented by mask has no internal conflicts
# - Find maximum |mask| where dp[mask] = 1 AND all PRs in mask are mergeable
#
# For larger n, we fall back to a greedy approximation.

# Build adjacency matrix for conflict graph
#
# Args:
#   ralph_dir - Ralph directory path
#   task_ids  - Array of task IDs (passed by name)
#
# Sets global: _CONFLICT_MATRIX[i*n+j] = 1 if tasks i and j conflict
_build_conflict_matrix() {
    local ralph_dir="$1"
    local -n _task_array="$2"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    local n=${#_task_array[@]}
    _CONFLICT_MATRIX=()

    # Initialize matrix to 0
    local i j
    for ((i=0; i<n; i++)); do
        for ((j=0; j<n; j++)); do
            _CONFLICT_MATRIX[i*n+j]=0
        done
    done

    # Fill in conflicts
    for ((i=0; i<n; i++)); do
        local task_i="${_task_array[$i]}"
        local conflicts
        conflicts=$(jq -r --arg t "$task_i" '.conflict_graph[$t] // [] | .[]' "$state_file")

        while IFS= read -r conflict_task; do
            [ -n "$conflict_task" ] || continue
            # Find index of conflict_task
            for ((j=0; j<n; j++)); do
                if [ "${_task_array[$j]}" = "$conflict_task" ]; then
                    _CONFLICT_MATRIX[i*n+j]=1
                    _CONFLICT_MATRIX[j*n+i]=1
                    break
                fi
            done
        done <<< "$conflicts"
    done
}

# Check if a subset (bitmask) is an independent set (no internal conflicts)
#
# Args:
#   mask - Bitmask representing subset
#   n    - Number of tasks
#
# Returns: 0 if independent set, 1 otherwise
_is_independent_set() {
    local mask="$1"
    local n="$2"

    local i j
    for ((i=0; i<n; i++)); do
        # Skip if i not in mask
        (( (mask >> i) & 1 )) || continue

        for ((j=i+1; j<n; j++)); do
            # Skip if j not in mask
            (( (mask >> j) & 1 )) || continue

            # Check if i and j conflict
            if [ "${_CONFLICT_MATRIX[i*n+j]}" = "1" ]; then
                return 1  # Not independent
            fi
        done
    done

    return 0  # Is independent
}

# Count bits set in a number (population count)
_popcount() {
    local n="$1"
    local count=0
    while [ "$n" -gt 0 ]; do
        ((count += n & 1))
        ((n >>= 1))
    done
    echo "$count"
}

# Find Maximum Independent Set using bitmask DP
#
# Args:
#   ralph_dir    - Ralph directory path
#   task_ids     - Array of task IDs (passed by name)
#   mergeable    - Array of 0/1 indicating if task is currently mergeable (passed by name)
#
# Returns: JSON array of task IDs in the maximum independent set
_find_maximum_independent_set() {
    local ralph_dir="$1"
    local -n _tasks="$2"
    local -n _mergeable="$3"

    local n=${#_tasks[@]}

    # For n > 20, use greedy fallback (2^20 = 1M iterations is borderline)
    if [ "$n" -gt 18 ]; then
        log "  Using greedy approximation (n=$n > 18)"
        _find_mis_greedy "$ralph_dir" _tasks _mergeable
        return
    fi

    # Build conflict matrix
    _build_conflict_matrix "$ralph_dir" _tasks

    local max_mask=0
    local max_mergeable_count=0
    local max_total_count=0

    # Iterate through all subsets
    local total=$((1 << n))
    local mask

    for ((mask=1; mask<total; mask++)); do
        # Quick filter: skip if this mask has fewer mergeable than current best
        local mergeable_count=0
        local total_count=0
        local i

        for ((i=0; i<n; i++)); do
            if (( (mask >> i) & 1 )); then
                ((++total_count))
                if [ "${_mergeable[$i]}" = "1" ]; then
                    ((++mergeable_count))
                fi
            fi
        done

        # Skip if can't beat current best
        # Primary: maximize mergeable count
        # Secondary: maximize total count
        if [ "$mergeable_count" -lt "$max_mergeable_count" ]; then
            continue
        fi
        if [ "$mergeable_count" -eq "$max_mergeable_count" ] && [ "$total_count" -le "$max_total_count" ]; then
            continue
        fi

        # Check if this is a valid independent set
        if _is_independent_set "$mask" "$n"; then
            max_mask=$mask
            max_mergeable_count=$mergeable_count
            max_total_count=$total_count
        fi
    done

    # Convert mask to task IDs
    local result="[]"
    for ((i=0; i<n; i++)); do
        if (( (max_mask >> i) & 1 )); then
            result=$(echo "$result" | jq --arg t "${_tasks[$i]}" '. + [$t]')
        fi
    done

    echo "$result"
}

# Greedy approximation for Maximum Independent Set (for large n)
#
# Strategy: Repeatedly pick the vertex with minimum degree, add to set, remove neighbors
#
# Args:
#   ralph_dir    - Ralph directory path
#   task_ids     - Array of task IDs (passed by name)
#   mergeable    - Array of 0/1 indicating if task is currently mergeable (passed by name)
#
# Returns: JSON array of task IDs in the independent set
_find_mis_greedy() {
    local ralph_dir="$1"
    local -n _tasks_g="$2"
    local -n _mergeable_g="$3"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    local n=${#_tasks_g[@]}
    local -a removed=()
    local -a in_set=()

    # Initialize
    for ((i=0; i<n; i++)); do
        removed[$i]=0
        in_set[$i]=0
    done

    # Build conflict matrix if not already built
    _build_conflict_matrix "$ralph_dir" _tasks_g

    # Greedy: prioritize mergeable PRs, then minimum degree
    while true; do
        local best_idx=-1
        local best_degree=999999
        local best_mergeable=0

        for ((i=0; i<n; i++)); do
            [ "${removed[$i]}" = "1" ] && continue

            # Calculate current degree (conflicts with non-removed nodes)
            local degree=0
            for ((j=0; j<n; j++)); do
                [ "${removed[$j]}" = "1" ] && continue
                [ "$i" = "$j" ] && continue
                if [ "${_CONFLICT_MATRIX[i*n+j]}" = "1" ]; then
                    ((++degree))
                fi
            done

            local is_mergeable="${_mergeable_g[$i]}"

            # Prefer: mergeable > non-mergeable, then lower degree
            if [ "$best_idx" = "-1" ]; then
                best_idx=$i
                best_degree=$degree
                best_mergeable=$is_mergeable
            elif [ "$is_mergeable" = "1" ] && [ "$best_mergeable" = "0" ]; then
                best_idx=$i
                best_degree=$degree
                best_mergeable=$is_mergeable
            elif [ "$is_mergeable" = "$best_mergeable" ] && [ "$degree" -lt "$best_degree" ]; then
                best_idx=$i
                best_degree=$degree
                best_mergeable=$is_mergeable
            fi
        done

        # No more nodes to add
        [ "$best_idx" = "-1" ] && break

        # Add best to set
        in_set[$best_idx]=1
        removed[$best_idx]=1

        # Remove all neighbors
        for ((j=0; j<n; j++)); do
            if [ "${_CONFLICT_MATRIX[best_idx*n+j]}" = "1" ]; then
                removed[$j]=1
            fi
        done
    done

    # Convert to JSON
    local result="[]"
    for ((i=0; i<n; i++)); do
        if [ "${in_set[$i]}" = "1" ]; then
            result=$(echo "$result" | jq --arg t "${_tasks_g[$i]}" '. + [$t]')
        fi
    done

    echo "$result"
}

# Calculate priority score for tiebreaking within independent set
# Used to order PRs within a merge batch
#
# Prioritizes PRs that unblock the most downstream tasks (dependency chain),
# then by simplicity (fewer files, fewer conflicts).
#
# Args:
#   ralph_dir - Ralph directory path
#   task_id   - Task identifier
#
# Returns: Integer priority score (higher = merge first)
_calculate_merge_priority() {
    local ralph_dir="$1"
    local task_id="$2"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    local kanban_file="$ralph_dir/kanban.md"

    # More blocked tasks = higher priority (unblock more work)
    # This is the MOST important factor - tasks that unblock others should merge first
    local dep_depth=0
    if [ -f "$kanban_file" ]; then
        dep_depth=$(get_dependency_depth "$kanban_file" "$task_id" 2>/dev/null || echo "0")
    fi

    # Fewer files = simpler PR = merge first (tiebreaker)
    local files_count
    files_count=$(jq -r --arg t "$task_id" '.prs[$t].files_modified | length' "$state_file")

    # Fewer conflicts = less likely to cause issues (tiebreaker)
    local conflict_count
    conflict_count=$(jq -r --arg t "$task_id" '.conflict_graph[$t] // [] | length' "$state_file")

    # Score: higher = merge first
    # Dependency depth is weighted heavily (100 points per blocked task)
    # This ensures tasks that unblock others are prioritized
    local score=1000
    ((score += dep_depth * 100)) || true
    ((score -= files_count * 10)) || true
    ((score -= conflict_count * 50)) || true

    echo "$score"
}

# Find optimal merge order using Maximum Independent Set DP
#
# Strategy:
# 1. Find MIS among currently-mergeable PRs (maximize merge batch)
# 2. Order batch by tiebreaker priority (simpler PRs first)
# 3. Remaining PRs ordered by conflict count (for future passes)
#
# Args:
#   ralph_dir - Ralph directory path
pr_merge_find_optimal_order() {
    local ralph_dir="$1"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    log_debug "Phase 3: Finding optimal merge order..."

    # Get all task IDs and build arrays
    local -a task_array=()
    local -a mergeable_array=()

    local task_ids
    task_ids=$(jq -r '.prs | keys[]' "$state_file")

    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue
        task_array+=("$task_id")

        # Check ALL preconditions for merge-readiness:
        # 1. No conflicts with main
        # 2. No unaddressed comments
        # 3. Copilot review addressed (if requested)
        local is_mergeable has_comments copilot_ok
        is_mergeable=$(jq -r --arg t "$task_id" '.prs[$t].mergeable_to_main' "$state_file")
        has_comments=$(jq -r --arg t "$task_id" '.prs[$t].has_new_comments' "$state_file")
        copilot_ok=$(jq -r --arg t "$task_id" '.prs[$t].copilot_reviewed' "$state_file")

        if [ "$is_mergeable" = "true" ] && [ "$has_comments" != "true" ] && [ "$copilot_ok" = "true" ]; then
            mergeable_array+=(1)
        else
            mergeable_array+=(0)
        fi
    done <<< "$task_ids"

    local n=${#task_array[@]}

    if [ "$n" -eq 0 ]; then
        jq '.merge_order = []' "$state_file" > "$state_file.tmp"
        mv "$state_file.tmp" "$state_file"
        log "  No PRs to order"
        return
    fi

    log "  Processing $n PRs..."

    # Find Maximum Independent Set
    local mis_json
    mis_json=$(_find_maximum_independent_set "$ralph_dir" task_array mergeable_array)

    local mis_count
    mis_count=$(echo "$mis_json" | jq 'length')
    log "  Maximum Independent Set size: $mis_count"

    # Sort MIS by priority for merge order
    local -A priorities
    local task_id
    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue
        priorities[$task_id]=$(_calculate_merge_priority "$ralph_dir" "$task_id")
    done < <(echo "$mis_json" | jq -r '.[]')

    local sorted_mis=()
    for task_id in "${!priorities[@]}"; do
        sorted_mis+=("${priorities[$task_id]}|$task_id")
    done

    local merge_order=()
    while IFS= read -r entry; do
        [ -n "$entry" ] || continue
        local tid
        tid=$(echo "$entry" | cut -d'|' -f2)
        merge_order+=("$tid")
    done < <(printf '%s\n' "${sorted_mis[@]}" | sort -t'|' -k1 -rn)

    # Add remaining PRs (not in MIS) ordered by conflict count
    local -A remaining_priorities
    for task_id in "${task_array[@]}"; do
        # Skip if in MIS
        if echo "$mis_json" | jq -e --arg t "$task_id" 'index($t)' >/dev/null 2>&1; then
            continue
        fi
        remaining_priorities[$task_id]=$(_calculate_merge_priority "$ralph_dir" "$task_id")
    done

    local sorted_remaining=()
    for task_id in "${!remaining_priorities[@]}"; do
        sorted_remaining+=("${remaining_priorities[$task_id]}|$task_id")
    done

    while IFS= read -r entry; do
        [ -n "$entry" ] || continue
        local tid
        tid=$(echo "$entry" | cut -d'|' -f2)
        merge_order+=("$tid")
    done < <(printf '%s\n' "${sorted_remaining[@]}" | sort -t'|' -k1 -rn)

    # Build JSON array
    local order_json="[]"
    for task_id in "${merge_order[@]}"; do
        order_json=$(echo "$order_json" | jq --arg t "$task_id" '. + [$t]')
    done

    # Save to state with MIS info
    jq --argjson order "$order_json" --argjson mis "$mis_json" '
        .merge_order = $order |
        .optimal_batch = $mis
    ' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    log "  Optimal batch (MIS): $(echo "$mis_json" | jq -r 'join(", ")')"
    log "  Full merge order: $(echo "$order_json" | jq -r 'join(" → ")')"
}
