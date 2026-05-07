#!/usr/bin/env bash
# =============================================================================
# orphan-recovery.sh - Stale claim detection and recovery
#
# Detects tasks with stale heartbeats (server crashed/disconnected) and
# allows recovery by other servers.
#
# Recovery protocol:
#   1. Detect stale claims (heartbeat > threshold)
#   2. Post orphan recovery comment
#   3. Remove old server's labels/assignee
#   4. Allow any server to reclaim
#
# Service integration:
#   - Called periodically by orchestrator
#   - Default interval: 5 minutes
#   - Default stale threshold: 10 minutes
# =============================================================================
set -euo pipefail

[ -n "${_ORPHAN_RECOVERY_LOADED:-}" ] && return 0
_ORPHAN_RECOVERY_LOADED=1

# Source dependencies
[ -z "${_WIGGUM_SRC_LOGGER_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/logger.sh"
[ -z "${_WIGGUM_SRC_PLATFORM_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"

# =============================================================================
# Configuration
# =============================================================================

# Default stale threshold (seconds) - 10 minutes
_ORPHAN_STALE_THRESHOLD="${SERVER_STALE_THRESHOLD:-600}"

# Minimum time between orphan scans (seconds)
_ORPHAN_SCAN_INTERVAL=300

# Last scan timestamp
_ORPHAN_LAST_SCAN=0

# =============================================================================
# Core Functions
# =============================================================================

# Detect orphan claims (stale heartbeats)
#
# Scans all claimed tasks and identifies those with stale heartbeats.
#
# Args:
#   threshold - Stale threshold in seconds (optional)
#
# Returns: Lines of "issue_number|owner|age_seconds" on stdout
orphan_detect_stale_claims() {
    local threshold="${1:-$_ORPHAN_STALE_THRESHOLD}"

    claim_find_stale "$threshold"
}

# Recover a single orphan task
#
# Releases the stale claim and makes task available for any server.
#
# Args:
#   issue_number - GitHub issue number
#   old_owner    - Previous owner server ID
#   ralph_dir    - Path to .ralph directory (optional)
#
# Returns: 0 on success
orphan_recover_task() {
    local issue_number="$1"
    local old_owner="$2"
    local ralph_dir="${3:-}"

    log "Recovering orphan task #$issue_number from stale owner $old_owner"

    # Get age for logging
    local heartbeat_time age now
    heartbeat_time=$(claim_get_heartbeat_time "$issue_number")
    now=$(epoch_now)
    age=$((now - heartbeat_time))

    # Remove old server label
    local old_label="wiggum:server:${old_owner}"
    gh issue edit "$issue_number" --remove-label "$old_label" 2>/dev/null || true

    # Remove assignee(s)
    local assignees
    assignees=$(gh issue view "$issue_number" --json assignees --jq '.assignees[].login' 2>/dev/null) || true
    while IFS= read -r assignee; do
        [ -n "$assignee" ] || continue
        gh issue edit "$issue_number" --remove-assignee "$assignee" 2>/dev/null || true
    done <<< "$assignees"

    # Post recovery comment
    local recovery_comment
    recovery_comment="<!-- wiggum:orphan-recovery -->
**Orphan Recovery**

This task was claimed by server \`$old_owner\` but no heartbeat was received for $((age / 60)) minutes (threshold: $((_ORPHAN_STALE_THRESHOLD / 60)) minutes).

The task has been released and is now available for any server to claim.

**Previous Owner:** $old_owner
**Last Heartbeat:** $heartbeat_time seconds ago
**Recovery Time:** $(iso_now)"

    gh issue comment "$issue_number" --body "$recovery_comment" 2>/dev/null || true

    # Update status label to pending
    source "$WIGGUM_HOME/lib/tasks/task-source-github.sh"
    local pending_label="${_GH_STATUS_LABELS[" "]:-wiggum:pending}"
    local in_progress_label="${_GH_STATUS_LABELS["="]:-wiggum:in-progress}"

    # Remove in-progress label if present
    gh issue edit "$issue_number" --remove-label "$in_progress_label" 2>/dev/null || true
    # Add pending label
    gh issue edit "$issue_number" --add-label "$pending_label" 2>/dev/null || true

    log "Recovered orphan task #$issue_number (was stale for ${age}s)"
    return 0
}

# Recover all detected orphan tasks
#
# Scans for and recovers all stale claims.
#
# Args:
#   threshold - Stale threshold in seconds (optional)
#   ralph_dir - Path to .ralph directory (optional)
#
# Returns: Number of recovered tasks on stdout
orphan_recover_all() {
    local threshold="${1:-$_ORPHAN_STALE_THRESHOLD}"
    local ralph_dir="${2:-}"

    local stale_claims
    stale_claims=$(orphan_detect_stale_claims "$threshold")

    local recovered=0
    while IFS='|' read -r issue_number owner age; do
        [ -n "$issue_number" ] || continue

        if orphan_recover_task "$issue_number" "$owner" "$ralph_dir"; then
            ((++recovered))
        fi
    done <<< "$stale_claims"

    echo "$recovered"
}

# =============================================================================
# Service Integration
# =============================================================================

# Run orphan recovery scan
#
# Called by orchestrator periodic service. Includes throttling to avoid
# excessive API calls.
#
# Args:
#   ralph_dir - Path to .ralph directory
#   server_id - Our server ID (to avoid recovering our own tasks)
#   threshold - Stale threshold in seconds (optional)
#
# Returns: 0 on success
orphan_run_scan() {
    local ralph_dir="$1"
    local server_id="$2"
    local threshold="${3:-$_ORPHAN_STALE_THRESHOLD}"

    # Throttle scans
    local now
    now=$(epoch_now)
    if [ $((now - _ORPHAN_LAST_SCAN)) -lt "$_ORPHAN_SCAN_INTERVAL" ]; then
        log_debug "Skipping orphan scan (throttled)"
        return 0
    fi
    _ORPHAN_LAST_SCAN=$now

    log_debug "Running orphan recovery scan (threshold: ${threshold}s)"

    # Populate issue cache for task_id resolution (needed to check for workers)
    if declare -F _github_refresh_cache &>/dev/null; then
        _github_refresh_cache 2>/dev/null || true
    fi

    # Find stale claims
    local stale_claims
    stale_claims=$(orphan_detect_stale_claims "$threshold")

    if [ -z "$stale_claims" ]; then
        log_debug "No orphan tasks found"
        return 0
    fi

    # Process each stale claim
    local recovered=0
    while IFS='|' read -r issue_number owner age; do
        [ -n "$issue_number" ] || continue

        # Skip our own tasks only if we have a worker for them
        # (workerless claims get no heartbeat and would stay stale forever)
        if [ "$owner" = "$server_id" ]; then
            local has_worker=false
            local task_id=""
            if [ -n "${_GH_ISSUE_CACHE[$issue_number]+x}" ] && declare -F _github_parse_task_id &>/dev/null; then
                task_id=$(_github_parse_task_id "${_GH_ISSUE_CACHE[$issue_number]}") || true
            fi
            if [ -n "$task_id" ] && [ -d "$ralph_dir/workers" ]; then
                local worker_dir
                worker_dir=$(find "$ralph_dir/workers" -maxdepth 1 -type d \
                    -name "worker-${task_id}-*" 2>/dev/null | head -1)
                [ -n "$worker_dir" ] && has_worker=true
            fi
            if [ "$has_worker" = true ]; then
                log_debug "Skipping our own stale task #$issue_number ($task_id) - has worker"
                continue
            fi
            if [ -z "$task_id" ]; then
                log_debug "Skipping our own stale task #$issue_number - cannot resolve task_id"
                continue
            fi
            log "Self-recovering workerless claim on issue #$issue_number ($task_id)"
        fi

        log "Found orphan task #$issue_number (owner: $owner, stale: ${age}s)"

        if orphan_recover_task "$issue_number" "$owner" "$ralph_dir"; then
            ((++recovered))
        fi
    done <<< "$stale_claims"

    if [ "$recovered" -gt 0 ]; then
        log "Recovered $recovered orphan task(s)"
    fi

    return 0
}

# =============================================================================
# Reclaim Functions
# =============================================================================

# Attempt to reclaim a recovered orphan task
#
# After orphan recovery, any server can claim. This function attempts to
# claim if the task is ready and we have capacity.
#
# Args:
#   issue_number  - GitHub issue number
#   server_id     - Our server ID
#   ralph_dir     - Path to .ralph directory
#   max_tasks     - Maximum concurrent tasks (for capacity check)
#
# Returns: 0 if claimed, 1 if not claimed
orphan_try_reclaim() {
    local issue_number="$1"
    local server_id="$2"
    local ralph_dir="$3"
    local max_tasks="${4:-4}"

    # Check if task is claimable (no owner)
    local current_owner
    current_owner=$(claim_get_owner "$issue_number")
    if [ -n "$current_owner" ]; then
        log_debug "Task #$issue_number already claimed by $current_owner"
        return 1
    fi

    # Check our capacity
    local current_claims
    current_claims=$(claim_list_owned "$server_id" | wc -l)
    current_claims="${current_claims:-0}"

    if [ "$current_claims" -ge "$max_tasks" ]; then
        log_debug "At capacity ($current_claims/$max_tasks), not claiming #$issue_number"
        return 1
    fi

    # Attempt to claim
    if claim_task "$issue_number" "$server_id" "$ralph_dir"; then
        log "Reclaimed orphan task #$issue_number"
        return 0
    fi

    return 1
}

# Scan and optionally reclaim orphan tasks
#
# Combined operation: detect stale claims, recover them, and optionally
# attempt to claim for this server.
#
# Args:
#   ralph_dir  - Path to .ralph directory
#   server_id  - Our server ID
#   threshold  - Stale threshold in seconds (optional)
#   reclaim    - "true" to attempt reclaiming (optional)
#   max_tasks  - Maximum concurrent tasks (optional)
#
# Returns: 0 on success
orphan_scan_and_reclaim() {
    local ralph_dir="$1"
    local server_id="$2"
    local threshold="${3:-$_ORPHAN_STALE_THRESHOLD}"
    local reclaim="${4:-false}"
    local max_tasks="${5:-4}"

    # Run recovery scan
    orphan_run_scan "$ralph_dir" "$server_id" "$threshold"

    if [ "$reclaim" != "true" ]; then
        return 0
    fi

    # Attempt to claim any unclaimed tasks
    local gate_label="wiggum:task"
    local pending_label="wiggum:pending"

    # Find unclaimed pending tasks
    local unclaimed
    unclaimed=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh issue list \
        --label "$gate_label" \
        --label "$pending_label" \
        --state open \
        --json number,labels \
        --limit 20 2>/dev/null) || return 0

    local count i
    count=$(echo "$unclaimed" | jq 'length')

    for ((i=0; i<count; i++)); do
        local number labels has_owner
        number=$(echo "$unclaimed" | jq -r ".[$i].number")
        labels=$(echo "$unclaimed" | jq ".[$i].labels")

        # Check if has owner
        has_owner=$(echo "$labels" | jq -r \
            '[.[].name | select(startswith("wiggum:server:"))] | length')

        if [ "$has_owner" -eq 0 ]; then
            orphan_try_reclaim "$number" "$server_id" "$ralph_dir" "$max_tasks" || true
        fi
    done

    return 0
}

# =============================================================================
# Status/Reporting
# =============================================================================

# Get orphan recovery status
#
# Returns summary of stale claims and recovery stats.
#
# Args:
#   ralph_dir - Path to .ralph directory
#   threshold - Stale threshold in seconds (optional)
#
# Returns: JSON object on stdout
orphan_get_status() {
    local ralph_dir="$1"
    local threshold="${2:-$_ORPHAN_STALE_THRESHOLD}"

    local stale_claims
    stale_claims=$(orphan_detect_stale_claims "$threshold")

    local stale_count=0
    local stale_list="[]"

    if [ -n "$stale_claims" ]; then
        stale_count=$(echo "$stale_claims" | grep -c '^' || echo 0)

        # Build JSON array of stale claims
        stale_list="["
        local first=true
        while IFS='|' read -r issue_number owner age; do
            [ -n "$issue_number" ] || continue

            if [ "$first" != "true" ]; then
                stale_list="$stale_list,"
            fi
            first=false

            stale_list="$stale_list{\"issue\":$issue_number,\"owner\":\"$owner\",\"age\":$age}"
        done <<< "$stale_claims"
        stale_list="$stale_list]"
    fi

    jq -n \
        --argjson stale_count "$stale_count" \
        --argjson stale_claims "$stale_list" \
        --argjson threshold "$threshold" \
        --argjson last_scan "$_ORPHAN_LAST_SCAN" \
        '{
            stale_count: $stale_count,
            stale_claims: $stale_claims,
            threshold_seconds: $threshold,
            last_scan_epoch: $last_scan
        }'
}
