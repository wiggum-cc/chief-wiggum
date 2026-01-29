#!/usr/bin/env bash
# =============================================================================
# service-scheduler.sh - Service scheduling and state management
#
# This is a consolidated module that provides:
#   - Scheduling loop for declaratively-configured services
#   - State persistence and recovery (via service-state.sh)
#   - Core service functionality (via service-core.sh)
#
# Users should source this file for full service scheduler functionality.
# It automatically provides all service-core.sh and service-state.sh functions.
#
# Scheduler Functions:
#   service_scheduler_init()          - Initialize scheduler state
#   service_scheduler_tick()          - Check and run due services
#   service_scheduler_shutdown()      - Clean shutdown
#   service_scheduler_run_startup()   - Run services with run_on_startup
#   service_scheduler_status()        - Get scheduler status summary
#   service_scheduler_service_status(id) - Get status for specific service
#   service_scheduler_all_statuses()  - Get all service statuses
#   service_scheduler_set_group_enabled(group, enabled) - Enable/disable group
#   service_is_due(id)                - Check if interval service should run
#   service_trigger_event(event)      - Trigger event-based services
#
# State Functions (from service-state.sh):
#   service_state_init(ralph_dir)     - Initialize state tracking
#   service_state_save()              - Persist state to disk
#   service_state_restore()           - Load state from disk
#   service_state_get_status(id)      - Get service status
#   service_state_get_last_run(id)    - Get last run timestamp
#   service_state_get_metrics(id)     - Get service metrics
#   service_state_is_running(id)      - Check if service is running
#   service_state_mark_started(id)    - Mark service as started
#   service_state_mark_completed(id)  - Mark service as completed
#   service_state_mark_failed(id)     - Mark service as failed
#   service_state_queue_add(id, priority, args) - Add to execution queue
#   service_state_queue_pop(id)       - Pop from execution queue
#   service_state_get_circuit_state(id) - Get circuit breaker state
#
# Core Functions (from service-core.sh):
#   See service-core.sh for full list of configuration and execution functions
# =============================================================================

# Prevent double-sourcing
[ -n "${_SERVICE_SCHEDULER_LOADED:-}" ] && return 0
_SERVICE_SCHEDULER_LOADED=1

# Source dependencies - use consolidated service-core.sh
source "$WIGGUM_HOME/lib/service/service-core.sh"
source "$WIGGUM_HOME/lib/service/service-state.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"

# Scheduler configuration
_SCHED_RALPH_DIR=""
_SCHED_PROJECT_DIR=""
_SCHED_INITIALIZED=false
_SCHED_STARTUP_COMPLETE=false
_SCHED_LAST_HEALTH_CHECK=0
_SCHED_HEALTH_CHECK_INTERVAL=30

# Track last cron minute to avoid duplicate runs
declare -gA _SCHED_LAST_CRON_MINUTE=()

# Initialize the service scheduler
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
service_scheduler_init() {
    local ralph_dir="$1"
    local project_dir="$2"

    _SCHED_RALPH_DIR="$ralph_dir"
    _SCHED_PROJECT_DIR="$project_dir"

    # Initialize state tracking
    service_state_init "$ralph_dir"

    # Try to restore previous state
    if service_state_restore; then
        log_debug "Restored previous service scheduler state"
    fi

    # Load service configuration
    local config_file="$WIGGUM_HOME/config/services.json"
    if [ -f "$config_file" ]; then
        if ! service_load "$config_file"; then
            log_warn "Failed to load service config, using built-in defaults"
            service_load_builtin_defaults
        fi
    else
        service_load_builtin_defaults
    fi

    # Load project overrides if present
    local override_file="$ralph_dir/services.json"
    if [ -f "$override_file" ]; then
        service_load_override "$override_file"
    fi

    # Initialize runner
    service_runner_init "$ralph_dir" "$project_dir"

    _SCHED_INITIALIZED=true
    _SCHED_STARTUP_COMPLETE=false
    _SCHED_LAST_HEALTH_CHECK=$(date +%s)

    log "Service scheduler initialized with $(service_count) services"
}

# Run startup services (those with run_on_startup: true)
#
# Called once after initialization to run services immediately.
service_scheduler_run_startup() {
    [ "$_SCHED_INITIALIZED" = true ] || return 1
    [ "$_SCHED_STARTUP_COMPLETE" = false ] || return 0

    log_debug "Running startup services..."

    local enabled_services
    enabled_services=$(service_get_enabled)

    for id in $enabled_services; do
        if service_runs_on_startup "$id"; then
            local schedule_type
            schedule_type=$(service_get_field "$id" ".schedule.type" "interval")

            # Only run interval and cron services on startup (event services need triggers)
            if [ "$schedule_type" = "interval" ] || [ "$schedule_type" = "cron" ]; then
                log_debug "Running startup service: $id"
                _run_service_if_allowed "$id"
            fi
        fi
    done

    _SCHED_STARTUP_COMPLETE=true
}

# One tick of the service scheduler
#
# Checks all enabled services and runs those that are due.
# Should be called periodically (e.g., every second in main loop).
service_scheduler_tick() {
    [ "$_SCHED_INITIALIZED" = true ] || return 1

    # Run startup services on first tick
    if [ "$_SCHED_STARTUP_COMPLETE" = false ]; then
        service_scheduler_run_startup
    fi

    local enabled_services
    enabled_services=$(service_get_enabled)

    for id in $enabled_services; do
        # Skip if circuit breaker is open
        if _circuit_breaker_blocks "$id"; then
            continue
        fi

        # Skip if in backoff
        if service_state_is_in_backoff "$id"; then
            log_debug "Service $id in backoff (${_SERVICE_BACKOFF_UNTIL[$id]:-0}s remaining)"
            continue
        fi

        # Skip if conditions not met
        if ! service_conditions_met "$id"; then
            continue
        fi

        # Skip if dependencies not satisfied
        if ! service_dependencies_satisfied "$id"; then
            continue
        fi

        local schedule_type
        schedule_type=$(service_get_field "$id" ".schedule.type" "interval")

        case "$schedule_type" in
            interval)
                if service_is_due "$id"; then
                    _run_service_if_allowed "$id"
                fi
                ;;
            cron)
                if _cron_service_is_due "$id"; then
                    _run_service_if_allowed "$id"
                fi
                ;;
            continuous)
                # Continuous services restart automatically when stopped
                if ! service_state_is_running "$id"; then
                    local restart_delay
                    restart_delay=$(service_get_field "$id" ".schedule.restart_delay" "5")
                    local last_run
                    last_run=$(service_state_get_last_run "$id")
                    local now
                    now=$(date +%s)

                    if [ $((now - last_run)) -ge "$restart_delay" ]; then
                        _run_service_if_allowed "$id"
                    fi
                fi
                ;;
            event)
                # Event services are triggered by service_trigger_event
                ;;
        esac
    done

    # Process queued executions
    _process_service_queues

    # Check for completed background services
    _check_completed_services

    # Run health checks periodically
    _maybe_run_health_checks

    # Periodically save state
    service_state_save
}

# Check if an interval service is due to run
#
# Takes jitter into account by adding random delay to the base interval.
#
# Args:
#   id - Service identifier
#
# Returns: 0 if due, 1 if not due
service_is_due() {
    local id="$1"

    local interval
    interval=$(service_get_interval "$id")
    [ "$interval" -gt 0 ] || return 1

    local jitter
    jitter=$(service_get_jitter "$id")

    local last_run
    last_run=$(service_state_get_last_run "$id")

    local now
    now=$(date +%s)

    local elapsed=$((now - last_run))

    # Calculate effective interval with jitter
    local effective_interval="$interval"
    if [ "$jitter" -gt 0 ]; then
        # Add random jitter (0 to jitter seconds)
        local random_jitter=$((RANDOM % (jitter + 1)))
        effective_interval=$((interval + random_jitter))
    fi

    local is_due=false
    [ "$elapsed" -ge "$effective_interval" ] && is_due=true

    log_debug "Service $id tick: elapsed=${elapsed}s interval=${effective_interval}s due=$is_due"

    [ "$is_due" = "true" ]
}

# Check if a cron-scheduled service is due to run
#
# Args:
#   id - Service identifier
#
# Returns: 0 if due, 1 if not due
_cron_service_is_due() {
    local id="$1"

    local cron_expr
    cron_expr=$(service_get_cron_expression "$id")
    [ -n "$cron_expr" ] || return 1

    local timezone
    timezone=$(service_get_field "$id" ".schedule.timezone" "UTC")

    # Get current minute to track if we already ran this minute
    local current_minute
    current_minute=$(TZ="$timezone" date +%Y%m%d%H%M)

    # Check if we already ran this minute
    if [ "${_SCHED_LAST_CRON_MINUTE[$id]:-}" = "$current_minute" ]; then
        return 1
    fi

    # Check if cron matches
    if service_cron_matches_now "$cron_expr" "$timezone"; then
        _SCHED_LAST_CRON_MINUTE[$id]="$current_minute"
        return 0
    fi

    return 1
}

# Trigger event-based services
#
# Args:
#   event - Event name (e.g., "worker.completed", "scheduling_event")
#   args  - Optional arguments to pass to service
service_trigger_event() {
    local event="$1"
    shift
    local args=("$@")

    [ "$_SCHED_INITIALIZED" = true ] || return 1

    local enabled_services
    enabled_services=$(service_get_enabled)

    for id in $enabled_services; do
        local schedule_type trigger
        schedule_type=$(service_get_field "$id" ".schedule.type" "interval")
        [ "$schedule_type" = "event" ] || continue

        trigger=$(service_get_field "$id" ".schedule.trigger" "")
        if [ "$trigger" = "$event" ]; then
            # Check conditions and dependencies even for events
            if ! service_conditions_met "$id"; then
                log_debug "Event '$event' for service $id skipped (conditions not met)"
                continue
            fi
            if ! service_dependencies_satisfied "$id"; then
                log_debug "Event '$event' for service $id skipped (dependencies not satisfied)"
                continue
            fi
            if _circuit_breaker_blocks "$id"; then
                log_debug "Event '$event' for service $id skipped (circuit open)"
                continue
            fi

            log_debug "Event '$event' triggered service: $id"
            _run_service_if_allowed "$id" "${args[@]}"
        fi
    done
}

# Run a service if concurrency rules allow
#
# Handles:
# - max_instances checking
# - if_running policy (skip, queue, kill)
# - Priority queuing
#
# Args:
#   id   - Service identifier
#   args - Additional arguments to pass to service
_run_service_if_allowed() {
    local id="$1"
    shift
    local args=("$@")

    # Check concurrency
    local concurrency
    concurrency=$(service_get_concurrency "$id")

    local max_instances if_running priority queue_max
    max_instances=$(echo "$concurrency" | jq -r '.max_instances // 1')
    if_running=$(echo "$concurrency" | jq -r '.if_running // "skip"')
    priority=$(echo "$concurrency" | jq -r '.priority // "normal"')
    queue_max=$(echo "$concurrency" | jq -r '.queue_max // 10')

    local running_count
    running_count=$(service_state_get_running_count "$id")

    if [ "$running_count" -ge "$max_instances" ]; then
        case "$if_running" in
            skip)
                log_debug "Skipping $id - already at max instances ($running_count/$max_instances)"
                service_state_mark_skipped "$id"
                return 0
                ;;
            queue)
                local queue_size
                queue_size=$(service_state_queue_size "$id")
                if [ "$queue_size" -ge "$queue_max" ]; then
                    log_debug "Queue full for $id ($queue_size/$queue_max), dropping"
                    return 0
                fi
                log_debug "Queueing $id - already running (queue size: $queue_size)"
                local args_json
                args_json=$(printf '%s\n' "${args[@]}" | jq -R . | jq -s .)
                service_state_queue_add "$id" "$priority" "$args_json"
                return 0
                ;;
            kill)
                # Stop the running instance
                local pid
                pid=$(service_state_get_pid "$id")
                if [ -n "$pid" ]; then
                    log_debug "Killing previous instance of $id (PID: $pid)"
                    kill "$pid" 2>/dev/null || true
                    # Wait briefly for process to exit
                    sleep 0.5
                fi
                ;;
        esac
    fi

    # Run the service
    service_run "$id" "${args[@]}"
}

# Process queued service executions
_process_service_queues() {
    local enabled_services
    enabled_services=$(service_get_enabled)

    for id in $enabled_services; do
        local queue_size
        queue_size=$(service_state_queue_size "$id")
        [ "$queue_size" -gt 0 ] || continue

        # Check if we can run now
        if service_state_is_running "$id"; then
            continue
        fi

        # Pop from queue and run
        local queued
        queued=$(service_state_queue_pop "$id")
        [ -n "$queued" ] || continue

        local args_json
        args_json=$(echo "$queued" | jq -c '.args // []')

        log_debug "Processing queued execution for $id"

        # Convert JSON array to bash array
        local -a args=()
        while IFS= read -r arg; do
            args+=("$arg")
        done < <(echo "$args_json" | jq -r '.[]')

        service_run "$id" "${args[@]}"
    done
}

# Check for completed background services and update their state
_check_completed_services() {
    local enabled_services
    enabled_services=$(service_get_enabled)

    for id in $enabled_services; do
        local status
        status=$(service_state_get_status "$id")

        if [ "$status" = "running" ]; then
            local pid
            pid=$(service_state_get_pid "$id")

            if [ -n "$pid" ] && ! kill -0 "$pid" 2>/dev/null; then
                # Process has exited
                # Check exit code from wait (if possible)
                wait "$pid" 2>/dev/null
                local exit_code=$?

                # Record metrics
                local start_time duration_ms
                start_time=$(service_state_get_last_run "$id")
                duration_ms=$(( ($(date +%s) - start_time) * 1000 ))
                service_state_record_execution "$id" "$duration_ms" "$exit_code"

                if [ "$exit_code" -eq 0 ]; then
                    service_state_mark_completed "$id"
                    log_debug "Service $id completed successfully"
                else
                    service_state_mark_failed "$id"
                    log_debug "Service $id failed (exit code: $exit_code)"
                    _handle_service_failure "$id"
                fi
            fi
        fi
    done
}

# Handle service failure according to restart policy and circuit breaker
_handle_service_failure() {
    local id="$1"

    # Update circuit breaker
    if service_circuit_breaker_enabled "$id"; then
        _update_circuit_breaker "$id"
    fi

    local restart_policy
    restart_policy=$(service_get_field "$id" ".restart_policy.on_failure" "skip")

    local max_retries
    max_retries=$(service_get_field "$id" ".restart_policy.max_retries" "2")

    local retry_count
    retry_count=$(service_state_get_retry_count "$id")

    case "$restart_policy" in
        retry)
            if [ "$retry_count" -lt "$max_retries" ]; then
                # Calculate backoff delay
                local backoff_delay
                backoff_delay=$(service_calculate_backoff "$id" "$retry_count")

                service_state_increment_retry "$id"
                service_state_set_backoff "$id" "$backoff_delay"

                log_debug "Retrying service $id in ${backoff_delay}s (attempt $((retry_count + 1))/$max_retries)"
            else
                log_warn "Service $id failed $retry_count times, giving up"
                service_state_reset_retry "$id"
            fi
            ;;
        skip)
            log_debug "Skipping retry for failed service $id"
            ;;
        abort)
            log_error "Service $id failed with abort policy"
            # Could signal scheduler to stop
            ;;
    esac
}

# Check if circuit breaker blocks service execution
#
# Args:
#   id - Service identifier
#
# Returns: 0 if blocked, 1 if allowed
_circuit_breaker_blocks() {
    local id="$1"

    # Skip if circuit breaker not enabled
    if ! service_circuit_breaker_enabled "$id"; then
        return 1
    fi

    local circuit_state
    circuit_state=$(service_state_get_circuit_state "$id")

    case "$circuit_state" in
        closed)
            return 1  # Allow execution
            ;;
        open)
            # Check if cooldown has passed
            local cb_config
            cb_config=$(service_get_circuit_breaker "$id")
            local cooldown
            cooldown=$(echo "$cb_config" | jq -r '.cooldown // 300')

            local opened_at
            opened_at=$(service_state_get_circuit_opened_at "$id")
            local now
            now=$(date +%s)

            if [ $((now - opened_at)) -ge "$cooldown" ]; then
                # Transition to half-open
                log_debug "Service $id circuit breaker transitioning to half-open"
                service_state_set_circuit_state "$id" "half-open"
                return 1  # Allow test request
            fi

            log_debug "Service $id blocked by open circuit (${cooldown}s cooldown)"
            return 0  # Block execution
            ;;
        half-open)
            # Allow limited test requests
            local cb_config
            cb_config=$(service_get_circuit_breaker "$id")
            local half_open_requests
            half_open_requests=$(echo "$cb_config" | jq -r '.half_open_requests // 1')

            local attempts
            attempts=$(service_state_get_half_open_attempts "$id")

            if [ "$attempts" -lt "$half_open_requests" ]; then
                service_state_increment_half_open_attempts "$id"
                return 1  # Allow test request
            fi

            return 0  # Block additional requests until result
            ;;
    esac

    return 1
}

# Update circuit breaker state after failure
_update_circuit_breaker() {
    local id="$1"

    local fail_count
    fail_count=$(service_state_get_fail_count "$id")

    local cb_config
    cb_config=$(service_get_circuit_breaker "$id")
    local threshold
    threshold=$(echo "$cb_config" | jq -r '.threshold // 5')

    local circuit_state
    circuit_state=$(service_state_get_circuit_state "$id")

    if [ "$circuit_state" = "half-open" ]; then
        # Failed during half-open, reopen circuit
        log_warn "Service $id failed in half-open state, reopening circuit"
        service_state_set_circuit_state "$id" "open"
    elif [ "$fail_count" -ge "$threshold" ]; then
        # Threshold reached, open circuit
        log_warn "Service $id circuit breaker opened after $fail_count failures"
        service_state_set_circuit_state "$id" "open"
    fi
}

# Run health checks on services that have them configured
_maybe_run_health_checks() {
    local now
    now=$(date +%s)

    # Only run health checks periodically
    if [ $((now - _SCHED_LAST_HEALTH_CHECK)) -lt "$_SCHED_HEALTH_CHECK_INTERVAL" ]; then
        return
    fi
    _SCHED_LAST_HEALTH_CHECK="$now"

    local enabled_services
    enabled_services=$(service_get_enabled)

    for id in $enabled_services; do
        # Only check running services with health checks
        if ! service_state_is_running "$id"; then
            continue
        fi
        if ! service_has_health_check "$id"; then
            continue
        fi

        _run_health_check "$id"
    done
}

# Run health check for a specific service
#
# Args:
#   id - Service identifier
_run_health_check() {
    local id="$1"

    local health_config
    health_config=$(service_get_health_check "$id")
    [ "$health_config" != "null" ] || return 0

    local health_type max_age on_unhealthy
    health_type=$(echo "$health_config" | jq -r '.type // "heartbeat"')
    max_age=$(echo "$health_config" | jq -r '.max_age // 60')
    on_unhealthy=$(echo "$health_config" | jq -r '.on_unhealthy // "log"')

    local healthy=true

    case "$health_type" in
        file)
            local health_path
            health_path=$(echo "$health_config" | jq -r '.path // ""')
            if [ -n "$health_path" ]; then
                if [ -f "$health_path" ]; then
                    # Check file age
                    local file_mtime now age
                    file_mtime=$(stat -c %Y "$health_path" 2>/dev/null || echo 0)
                    now=$(date +%s)
                    age=$((now - file_mtime))
                    if [ "$age" -gt "$max_age" ]; then
                        healthy=false
                        log_warn "Service $id health file $health_path is stale (${age}s old)"
                    fi
                else
                    healthy=false
                    log_warn "Service $id health file $health_path does not exist"
                fi
            fi
            ;;
        command)
            local health_cmd
            health_cmd=$(echo "$health_config" | jq -r '.command // ""')
            if [ -n "$health_cmd" ]; then
                if ! bash -c "$health_cmd" > /dev/null 2>&1; then
                    healthy=false
                    log_warn "Service $id health command failed"
                fi
            fi
            ;;
        heartbeat)
            # Check if service has updated its last_run recently
            local last_run now age
            last_run=$(service_state_get_last_run "$id")
            now=$(date +%s)
            age=$((now - last_run))
            if [ "$age" -gt "$max_age" ]; then
                healthy=false
                log_warn "Service $id has not updated heartbeat (${age}s)"
            fi
            ;;
    esac

    if [ "$healthy" = false ]; then
        case "$on_unhealthy" in
            restart)
                log_warn "Restarting unhealthy service $id"
                local pid
                pid=$(service_state_get_pid "$id")
                if [ -n "$pid" ]; then
                    kill "$pid" 2>/dev/null || true
                fi
                service_state_mark_failed "$id"
                ;;
            kill)
                log_warn "Killing unhealthy service $id"
                local pid
                pid=$(service_state_get_pid "$id")
                if [ -n "$pid" ]; then
                    kill -9 "$pid" 2>/dev/null || true
                fi
                service_state_mark_failed "$id"
                ;;
            log)
                # Already logged above
                ;;
        esac
    fi
}

# Clean shutdown of the scheduler
service_scheduler_shutdown() {
    [ "$_SCHED_INITIALIZED" = true ] || return 0

    log_debug "Shutting down service scheduler..."

    # Save final state
    service_state_save

    _SCHED_INITIALIZED=false
}

# Get scheduler status summary
#
# Returns: JSON object with scheduler status
service_scheduler_status() {
    local enabled_count running_count failed_count queued_count
    local circuit_open_count

    enabled_count=0
    running_count=0
    failed_count=0
    queued_count=0
    circuit_open_count=0

    local enabled_services
    enabled_services=$(service_get_enabled)

    for id in $enabled_services; do
        ((++enabled_count))

        local status
        status=$(service_state_get_status "$id")

        case "$status" in
            running) ((++running_count)) ;;
            failed) ((++failed_count)) ;;
        esac

        # Count queued items
        local queue_size
        queue_size=$(service_state_queue_size "$id")
        queued_count=$((queued_count + queue_size))

        # Count open circuits
        local circuit_state
        circuit_state=$(service_state_get_circuit_state "$id")
        [ "$circuit_state" = "open" ] && ((++circuit_open_count))
    done

    jq -n \
        --argjson enabled "$enabled_count" \
        --argjson running "$running_count" \
        --argjson failed "$failed_count" \
        --argjson queued "$queued_count" \
        --argjson circuit_open "$circuit_open_count" \
        --argjson initialized "$([[ "$_SCHED_INITIALIZED" = true ]] && echo true || echo false)" \
        '{
            "initialized": $initialized,
            "enabled_services": $enabled,
            "running_services": $running,
            "failed_services": $failed,
            "queued_executions": $queued,
            "circuit_breakers_open": $circuit_open
        }'
}

# Get detailed status for a specific service
#
# Args:
#   id - Service identifier
#
# Returns: JSON object with service status
service_scheduler_service_status() {
    local id="$1"

    local status last_run run_count fail_count interval
    status=$(service_state_get_status "$id")
    last_run=$(service_state_get_last_run "$id")
    run_count=$(service_state_get_run_count "$id")
    fail_count=$(service_state_get_fail_count "$id")
    interval=$(service_get_interval "$id")

    local now
    now=$(date +%s)

    local next_run_in=""
    if [ "$interval" -gt 0 ]; then
        local elapsed=$((now - last_run))
        local remaining=$((interval - elapsed))
        [ "$remaining" -lt 0 ] && remaining=0
        next_run_in="$remaining"
    fi

    local schedule_type
    schedule_type=$(service_get_field "$id" ".schedule.type" "interval")

    local description
    description=$(service_get_field "$id" ".description" "")

    local circuit_state
    circuit_state=$(service_state_get_circuit_state "$id")

    local queue_size
    queue_size=$(service_state_queue_size "$id")

    local metrics
    metrics=$(service_state_get_metrics "$id")

    local backoff_remaining
    backoff_remaining=$(service_state_get_backoff_remaining "$id")

    jq -n \
        --arg id "$id" \
        --arg status "$status" \
        --arg schedule_type "$schedule_type" \
        --argjson last_run "$last_run" \
        --argjson run_count "$run_count" \
        --argjson fail_count "$fail_count" \
        --argjson interval "$interval" \
        --arg next_run_in "${next_run_in:-null}" \
        --arg description "$description" \
        --arg circuit_state "$circuit_state" \
        --argjson queue_size "$queue_size" \
        --argjson metrics "$metrics" \
        --argjson backoff_remaining "$backoff_remaining" \
        '{
            "id": $id,
            "description": $description,
            "status": $status,
            "schedule_type": $schedule_type,
            "last_run": $last_run,
            "run_count": $run_count,
            "fail_count": $fail_count,
            "interval": $interval,
            "next_run_in": (if $next_run_in == "null" then null else ($next_run_in | tonumber) end),
            "circuit_state": $circuit_state,
            "queue_size": $queue_size,
            "backoff_remaining": $backoff_remaining,
            "metrics": $metrics
        }'
}

# Check if scheduler has completed (all services stopped, continuous tasks done)
#
# Returns: 0 if complete (can exit), 1 if still running
service_scheduler_is_complete() {
    # For now, always return 1 (never complete on its own)
    # The orchestrator handles completion logic
    return 1
}

# Enable or disable a service group
#
# Args:
#   group   - Group name
#   enabled - true or false
service_scheduler_set_group_enabled() {
    local group="$1"
    local enabled="$2"

    # This modifies the in-memory config
    # For persistent changes, update the override file
    if [ -n "$_SERVICE_JSON" ]; then
        _SERVICE_JSON=$(echo "$_SERVICE_JSON" | jq --arg g "$group" --argjson e "$enabled" \
            '.groups[$g].enabled = $e')
        log "Service group '$group' $([ "$enabled" = "true" ] && echo "enabled" || echo "disabled")"
    fi
}

# Get all services with their current status
#
# Returns: JSON array of service statuses
service_scheduler_all_statuses() {
    local result="[]"

    local enabled_services
    enabled_services=$(service_get_enabled)

    for id in $enabled_services; do
        local svc_status
        svc_status=$(service_scheduler_service_status "$id")
        result=$(echo "$result" | jq --argjson s "$svc_status" '. + [$s]')
    done

    echo "$result"
}
