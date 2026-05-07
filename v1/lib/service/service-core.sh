#!/usr/bin/env bash
# =============================================================================
# service-core.sh - Core service functionality (loading + execution)
#
# This is a consolidated facade that combines:
#   - service-loader.sh: Configuration loading, validation, and querying
#   - service-runner.sh: Service execution by type
#
# Users should source this file for core service functionality.
# The scheduler sources this automatically.
#
# Provides (from service-loader.sh):
#   service_load(file)                - Load and validate service configuration
#   service_load_override(file)       - Merge project-level service overrides
#   service_get_enabled()             - List enabled services
#   service_get_by_id(id)             - Get service definition as JSON
#   service_get_schedule(id)          - Get schedule config for a service
#   service_get_execution(id)         - Get execution config for a service
#   service_get_field(id, field, default) - Get a specific field from a service
#   service_count()                   - Return number of services
#   service_get_dependencies(id)      - Get service dependencies
#   service_get_condition(id)         - Get conditional execution rules
#   service_get_health_check(id)      - Get health check config
#   service_get_limits(id)            - Get resource limits
#   service_get_circuit_breaker(id)   - Get circuit breaker config
#   service_get_groups(id)            - Get groups a service belongs to
#   service_get_services_in_group(group) - Get all services in a group
#   service_is_group_enabled(group)   - Check if a group is enabled
#   service_get_jitter(id)            - Get jitter for interval scheduling
#   service_get_backoff(id)           - Get backoff config for retries
#   service_load_builtin_defaults()   - Load built-in service defaults
#
# Provides (from service-runner.sh):
#   service_runner_init(ralph_dir, project_dir) - Initialize runner
#   service_run(id, args...)                    - Execute a service
#   service_run_sync(id, args...)               - Run service synchronously
#   service_wait(id, timeout)                   - Wait for background service
#   service_stop(id, signal)                    - Stop a running service
#   service_stop_all()                          - Stop all running services
#   service_get_output(id, lines)               - Get service output/logs
# =============================================================================

# Prevent double-sourcing
[ -n "${_SERVICE_CORE_LOADED:-}" ] && return 0
_SERVICE_CORE_LOADED=1

# Source the component modules
source "$WIGGUM_HOME/lib/service/service-loader.sh"
source "$WIGGUM_HOME/lib/service/service-runner.sh"

# =============================================================================
# CONVENIENCE FUNCTIONS
# =============================================================================

# Initialize core service functionality
#
# Loads configuration and prepares the runner. This is a convenience function
# that combines service_load and service_runner_init.
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#   config_file - Optional config file (default: $WIGGUM_HOME/config/services.json)
#
# Returns: 0 on success, 1 on error
service_core_init() {
    local ralph_dir="$1"
    local project_dir="$2"
    local config_file="${3:-$WIGGUM_HOME/config/services.json}"

    # Load configuration
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

    return 0
}

# Check if a service can run based on all prerequisites
#
# Combines dependency, condition, and circuit breaker checks.
#
# Args:
#   id - Service identifier
#
# Returns: 0 if service can run, 1 if blocked
service_can_run() {
    local id="$1"

    # Check conditions
    if ! service_conditions_met "$id"; then
        return 1
    fi

    # Check dependencies
    if ! service_dependencies_satisfied "$id"; then
        return 1
    fi

    return 0
}

# Get a summary of service configuration for debugging
#
# Args:
#   id - Service identifier
#
# Returns: JSON summary of service config
service_get_summary() {
    local id="$1"

    local schedule execution
    schedule=$(service_get_schedule "$id")
    execution=$(service_get_execution "$id")

    local schedule_type exec_type interval timeout
    schedule_type=$(echo "$schedule" | jq -r '.type // "unknown"')
    exec_type=$(echo "$execution" | jq -r '.type // "unknown"')
    interval=$(service_get_interval "$id")
    timeout=$(service_get_timeout "$id")

    local deps groups
    deps=$(service_get_dependencies "$id" | tr '\n' ',' | sed 's/,$//')
    groups=$(service_get_groups "$id" | tr '\n' ',' | sed 's/,$//')

    jq -n \
        --arg id "$id" \
        --arg schedule_type "$schedule_type" \
        --arg exec_type "$exec_type" \
        --argjson interval "$interval" \
        --argjson timeout "$timeout" \
        --arg deps "$deps" \
        --arg groups "$groups" \
        '{
            "id": $id,
            "schedule_type": $schedule_type,
            "execution_type": $exec_type,
            "interval": $interval,
            "timeout": $timeout,
            "dependencies": (if $deps == "" then [] else ($deps | split(",")) end),
            "groups": (if $groups == "" then [] else ($groups | split(",")) end)
        }'
}
