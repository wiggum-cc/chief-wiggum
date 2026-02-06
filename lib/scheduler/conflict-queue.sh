#!/usr/bin/env bash
# conflict-queue.sh - Multi-PR conflict queue management
#
# Manages a queue of PRs that failed to merge due to conflicts. Groups related
# conflicts by shared files and coordinates batch resolution via LLM planner.
#
# Queue file: .ralph/batches/queue.json
# Format:
# {
#   "queue": [
#     {"task_id": "FEAT-001", "worker_dir": "...", "pr_number": 42, "affected_files": ["src/api.ts"], "batch_id": null}
#   ],
#   "batches": {
#     "batch-123": {"status": "planning", "task_ids": ["FEAT-001", "FEAT-002"], "common_files": ["src/api.ts"]}
#   }
# }
set -euo pipefail

[ -n "${_CONFLICT_QUEUE_LOADED:-}" ] && return 0
_CONFLICT_QUEUE_LOADED=1
source "$WIGGUM_HOME/lib/core/platform.sh"

# Source dependencies
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/core/safe-path.sh"

# Initialize conflict queue if it doesn't exist
#
# Args:
#   ralph_dir - Ralph directory path
conflict_queue_init() {
    local ralph_dir="$1"
    safe_path "$ralph_dir" "ralph_dir" || return 1
    local queue_file="$ralph_dir/batches/queue.json"

    mkdir -p "$ralph_dir/batches"
    if [ ! -f "$queue_file" ]; then
        echo '{"queue":[],"batches":{}}' > "$queue_file"
    fi
}

# Add a task to the conflict queue
#
# Args:
#   ralph_dir      - Ralph directory path
#   task_id        - Task identifier
#   worker_dir     - Worker directory path
#   pr_number      - PR number
#   affected_files - JSON array of affected file paths
#
# Returns: 0 on success
conflict_queue_add() {
    local ralph_dir="$1"
    local task_id="$2"
    local worker_dir="$3"
    local pr_number="$4"
    local affected_files="$5"

    local queue_file="$ralph_dir/batches/queue.json"
    conflict_queue_init "$ralph_dir"

    # Use file lock for concurrent access
    local lock_file="$ralph_dir/batches/.queue.lock"

    (
        flock -x 200

        # Check if task already in queue
        if jq -e ".queue[] | select(.task_id == \"$task_id\")" "$queue_file" >/dev/null 2>&1; then
            log "Task $task_id already in conflict queue"
            return 0
        fi

        # Add to queue
        local timestamp
        timestamp=$(iso_now)

        local entry
        entry=$(jq -n \
            --arg task_id "$task_id" \
            --arg worker_dir "$worker_dir" \
            --argjson pr_number "$pr_number" \
            --argjson affected_files "$affected_files" \
            --arg added_at "$timestamp" \
            '{
                task_id: $task_id,
                worker_dir: $worker_dir,
                pr_number: $pr_number,
                affected_files: $affected_files,
                added_at: $added_at,
                batch_id: null
            }')

        jq --argjson entry "$entry" '.queue += [$entry]' "$queue_file" > "$queue_file.tmp"
        mv "$queue_file.tmp" "$queue_file"

        log "Added $task_id to conflict queue (PR #$pr_number)"
    ) 200>"$lock_file"
}

# Remove a task from the conflict queue
#
# Args:
#   ralph_dir - Ralph directory path
#   task_id   - Task identifier
conflict_queue_remove() {
    local ralph_dir="$1"
    local task_id="$2"

    local queue_file="$ralph_dir/batches/queue.json"
    [ -f "$queue_file" ] || return 0

    local lock_file="$ralph_dir/batches/.queue.lock"

    (
        flock -x 200

        jq --arg task_id "$task_id" '.queue = [.queue[] | select(.task_id != $task_id)]' \
            "$queue_file" > "$queue_file.tmp"
        mv "$queue_file.tmp" "$queue_file"
    ) 200>"$lock_file"
}

# Group related conflicts by shared files
#
# Scans the queue and identifies tasks that have overlapping affected files.
# Tasks with common files should be resolved together.
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: JSON array of groups, each with task_ids and common_files
conflict_queue_group_related() {
    local ralph_dir="$1"

    local queue_file="$ralph_dir/batches/queue.json"
    [ -f "$queue_file" ] || { echo "[]"; return 0; }

    # Single jq program replaces O(N^2) bash+jq nested loops
    jq '
        [.queue[] | select(.batch_id == null)] |
        if length < 2 then []
        else
          . as $items |
          reduce range($items | length) as $i (
            {groups: [], processed: []};
            . as $state |
            if ($state.processed | index($items[$i].task_id)) then $state
            else
              ($items[$i].task_id) as $tid |
              ($items[$i].affected_files) as $tfiles |
              [range($items | length) |
                select(. != $i) |
                . as $j |
                select(($items[$j].task_id) as $oid | $state.processed | index($oid) | not) |
                select(
                  ($items[$j].affected_files) as $ofiles |
                  ([$tfiles[], $ofiles[]] | group_by(.) | map(select(length > 1)) | length) > 0
                )
              ] as $overlapping |
              if ($overlapping | length) > 0 then
                ($overlapping | map($items[.].task_id)) as $overlap_ids |
                ([$overlapping[] | $items[.].affected_files[]] + $tfiles |
                  group_by(.) | map(select(length > 1) | .[0]) | unique) as $common |
                $state |
                .groups += [{task_ids: ([$tid] + $overlap_ids), common_files: $common}] |
                .processed += ([$tid] + $overlap_ids)
              else
                $state |
                .processed += [$tid]
              end
            end
          ) | .groups
        end
    ' "$queue_file"
}

# Check if batch threshold is met
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: 0 if batch is ready, 1 otherwise
conflict_queue_batch_ready() {
    local ralph_dir="$1"

    local groups
    groups=$(conflict_queue_group_related "$ralph_dir")

    local count
    count=$(echo "$groups" | jq 'length // 0')
    count="${count:-0}"

    [ "$count" -gt 0 ]
}

# Create a batch from grouped conflicts
#
# Args:
#   ralph_dir - Ralph directory path
#   task_ids  - JSON array of task IDs to batch
#
# Returns: batch_id
conflict_queue_create_batch() {
    local ralph_dir="$1"
    local task_ids="$2"

    local queue_file="$ralph_dir/batches/queue.json"
    local lock_file="$ralph_dir/batches/.queue.lock"

    local batch_id
    batch_id="batch-$(epoch_now)"

    (
        flock -x 200

        # Get common files for these tasks
        local common_files='[]'
        while read -r task_id; do
            local files
            files=$(jq -r --arg id "$task_id" '.queue[] | select(.task_id == $id) | .affected_files' "$queue_file")
            if [ -n "$files" ] && [ "$files" != "null" ]; then
                common_files=$(jq -n --argjson a "$common_files" --argjson b "$files" \
                    '[$a[], $b[]] | unique')
            fi
        done < <(echo "$task_ids" | jq -r '.[]')

        # Create batch entry
        local batch
        batch=$(jq -n \
            --arg batch_id "$batch_id" \
            --argjson task_ids "$task_ids" \
            --argjson common_files "$common_files" \
            --arg created_at "$(iso_now)" \
            '{
                status: "pending",
                task_ids: $task_ids,
                common_files: $common_files,
                created_at: $created_at
            }')

        # Update queue: add batch and mark tasks
        jq --arg batch_id "$batch_id" --argjson batch "$batch" --argjson task_ids "$task_ids" '
            .batches[$batch_id] = $batch |
            .queue = [.queue[] | if (.task_id | IN($task_ids[])) then .batch_id = $batch_id else . end]
        ' "$queue_file" > "$queue_file.tmp"
        mv "$queue_file.tmp" "$queue_file"
    ) 200>"$lock_file"

    echo "$batch_id"
}

# Update batch status
#
# Args:
#   ralph_dir - Ralph directory path
#   batch_id  - Batch identifier
#   status    - New status (pending, planning, planned, resolving, resolved, failed)
conflict_queue_update_batch_status() {
    local ralph_dir="$1"
    local batch_id="$2"
    local status="$3"

    local queue_file="$ralph_dir/batches/queue.json"
    local lock_file="$ralph_dir/batches/.queue.lock"

    (
        flock -x 200

        jq --arg batch_id "$batch_id" --arg status "$status" \
            '.batches[$batch_id].status = $status' \
            "$queue_file" > "$queue_file.tmp"
        mv "$queue_file.tmp" "$queue_file"
    ) 200>"$lock_file"
}

# Get batch info
#
# Args:
#   ralph_dir - Ralph directory path
#   batch_id  - Batch identifier
#
# Returns: JSON object with batch info
conflict_queue_get_batch() {
    local ralph_dir="$1"
    local batch_id="$2"

    local queue_file="$ralph_dir/batches/queue.json"
    [ -f "$queue_file" ] || { echo "null"; return 1; }

    jq --arg batch_id "$batch_id" '.batches[$batch_id]' "$queue_file"
}

# Get batch status
#
# Args:
#   ralph_dir - Ralph directory path
#   batch_id  - Batch identifier
#
# Returns: Status string (pending, planning, planned, failed, etc.)
conflict_queue_get_batch_status() {
    local ralph_dir="$1"
    local batch_id="$2"

    local queue_file="$ralph_dir/batches/queue.json"
    [ -f "$queue_file" ] || { echo "unknown"; return 1; }

    jq -r --arg batch_id "$batch_id" '.batches[$batch_id].status // "unknown"' "$queue_file"
}

# Get task IDs for a batch
#
# Args:
#   ralph_dir - Ralph directory path
#   batch_id  - Batch identifier
#
# Returns: Newline-separated list of task IDs
conflict_queue_get_batch_tasks() {
    local ralph_dir="$1"
    local batch_id="$2"

    local queue_file="$ralph_dir/batches/queue.json"
    [ -f "$queue_file" ] || return 1

    jq -r --arg batch_id "$batch_id" '.batches[$batch_id].task_ids[]' "$queue_file"
}

# Get pending batches that need planning
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: JSON array of batch_ids
conflict_queue_get_pending_batches() {
    local ralph_dir="$1"

    local queue_file="$ralph_dir/batches/queue.json"
    [ -f "$queue_file" ] || { echo "[]"; return 0; }

    jq '[.batches | to_entries[] | select(.value.status == "pending") | .key]' "$queue_file"
}

# Build conflict-batch.json for the multi-pr-planner agent
#
# Args:
#   ralph_dir - Ralph directory path
#   batch_id  - Batch identifier
#   output_file - Path to write the batch file
#
# Returns: 0 on success
conflict_queue_build_batch_file() {
    local ralph_dir="$1"
    local batch_id="$2"
    local output_file="$3"

    local queue_file="$ralph_dir/batches/queue.json"

    local batch
    batch=$(jq --arg batch_id "$batch_id" '.batches[$batch_id]' "$queue_file")

    if [ "$batch" = "null" ]; then
        log_error "Batch $batch_id not found"
        return 1
    fi

    local task_ids common_files
    task_ids=$(echo "$batch" | jq '.task_ids')
    common_files=$(echo "$batch" | jq '.common_files')

    # Extract all task data in a single jq call (replaces ~7 jq calls per task)
    local all_task_data
    all_task_data=$(jq -c --argjson task_ids "$task_ids" --argjson common_files "$common_files" '
        [.queue[] | select(.task_id | IN($task_ids[])) |
        {
            task_id: .task_id,
            worker_dir: .worker_dir,
            pr_number: .pr_number,
            affected_files: .affected_files,
            conflict_files: ([.affected_files[], $common_files[]] | group_by(.) | map(select(length > 1) | .[0]))
        }]
    ' "$queue_file")

    # Add branch info (requires git, cannot be done in jq)
    local tasks="$all_task_data"
    local i=0
    while IFS=$'\x1e' read -r task_id worker_dir; do
        [ -z "$task_id" ] && continue
        local branch=""
        if [ -d "$worker_dir/workspace" ]; then
            branch=$(git -C "$worker_dir/workspace" rev-parse --abbrev-ref HEAD 2>/dev/null || true)
        fi
        tasks=$(echo "$tasks" | jq -c --arg branch "$branch" --argjson idx "$i" '.[$idx] += {branch: $branch}')
        ((++i)) || true
    done < <(echo "$all_task_data" | jq -r '.[] | [.task_id, .worker_dir] | join("\u001e")')

    # Write batch file with explicit merge_order for the planner to use
    jq -n \
        --arg batch_id "$batch_id" \
        --arg created_at "$(iso_now)" \
        --argjson common_files "$common_files" \
        --argjson tasks "$tasks" \
        --argjson merge_order "$task_ids" \
        '{
            batch_id: $batch_id,
            created_at: $created_at,
            common_files: $common_files,
            merge_order: $merge_order,
            tasks: $tasks
        }' > "$output_file"

    log "Built batch file: $output_file"
}

# Remove resolved tasks from queue and cleanup batch
#
# Args:
#   ralph_dir - Ralph directory path
#   batch_id  - Batch identifier
conflict_queue_cleanup_batch() {
    local ralph_dir="$1"
    local batch_id="$2"

    local queue_file="$ralph_dir/batches/queue.json"
    local lock_file="$ralph_dir/batches/.queue.lock"

    (
        flock -x 200

        # Remove tasks in this batch from queue
        jq --arg batch_id "$batch_id" '
            .queue = [.queue[] | select(.batch_id != $batch_id)] |
            del(.batches[$batch_id])
        ' "$queue_file" > "$queue_file.tmp"
        mv "$queue_file.tmp" "$queue_file"

        log "Cleaned up batch $batch_id"
    ) 200>"$lock_file"
}

# Get queue statistics
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: JSON object with queue stats
conflict_queue_stats() {
    local ralph_dir="$1"

    local queue_file="$ralph_dir/batches/queue.json"
    [ -f "$queue_file" ] || { echo '{"queued":0,"batched":0,"batches":0}'; return 0; }

    jq '{
        queued: [.queue[] | select(.batch_id == null)] | length,
        batched: [.queue[] | select(.batch_id != null)] | length,
        batches: .batches | length,
        by_status: (.batches | to_entries | group_by(.value.status) | map({key: .[0].value.status, value: length}) | from_entries)
    }' "$queue_file"
}
