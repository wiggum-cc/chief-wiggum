#!/usr/bin/env bash
# config-validator.sh - JSON schema validation for configuration files
#
# Provides validation functions for config.json and agents.json files
# using jq for JSON parsing. Reports helpful error messages for invalid config.
#
# Performance: Uses single jq calls to extract multiple values, reducing
# subprocess overhead from 25+ jq invocations to 2-3 per file.
set -euo pipefail

[ -n "${_CONFIG_VALIDATOR_LOADED:-}" ] && return 0
_CONFIG_VALIDATOR_LOADED=1

source "$WIGGUM_HOME/lib/core/logger.sh"

# Validate a JSON file exists and is valid JSON
#
# Args:
#   config_file - Path to JSON file to validate
#
# Returns: 0 if valid, 1 if invalid
validate_json_file() {
    local config_file="$1"

    if [ ! -f "$config_file" ]; then
        log_error "Config file not found: $config_file"
        return 1
    fi

    if ! jq empty "$config_file" 2>/dev/null; then
        log_error "Invalid JSON syntax in: $config_file"
        log_error "Run 'jq . $config_file' to see the error"
        return 1
    fi

    return 0
}

# Validate config.json against schema
#
# Args:
#   config_file - Path to config.json (defaults to $WIGGUM_HOME/config/config.json)
#
# Returns: 0 if valid, 1 if invalid
# shellcheck disable=SC2120
validate_config() {
    local config_file="${1:-$WIGGUM_HOME/config/config.json}"
    local errors=0

    log_debug "Validating config: $config_file"

    # First check JSON is valid
    if ! validate_json_file "$config_file"; then
        return 1
    fi

    # Single jq call extracts all values at once (performance optimization)
    # Output format: section_flags|max_iter|sleep_sec|hooks_enabled|fix_max_iter|fix_max_turns|approved_user_ids_type|keys
    # section_flags: 4-char string where each char is 1 (present) or 0 (missing) for workers,hooks,paths,review
    local extracted
    extracted=$(jq -r '
        [
            (if .workers then "1" else "0" end) +
            (if .hooks then "1" else "0" end) +
            (if .paths then "1" else "0" end) +
            (if .review then "1" else "0" end),
            (.workers.max_iterations // 50),
            (.workers.sleep_seconds // 2),
            (.hooks.enabled // "true"),
            (.review.fix_max_iterations // 10),
            (.review.fix_max_turns // 30),
            (if .review.approved_user_ids then (.review.approved_user_ids | type) else "null" end),
            (keys | join(","))
        ] | join("\u001e")
    ' "$config_file" 2>/dev/null)

    if [ -z "$extracted" ]; then
        log_error "Failed to parse config file: $config_file"
        return 1
    fi

    # Parse extracted values
    local section_flags max_iter sleep_sec hooks_enabled fix_max_iter fix_max_turns approved_type actual_keys
    IFS=$'\x1e' read -r section_flags max_iter sleep_sec hooks_enabled fix_max_iter fix_max_turns approved_type actual_keys <<< "$extracted"

    # Check optional sections and warn if missing
    local sections=("workers" "hooks" "paths" "review")
    local i
    for i in 0 1 2 3; do
        if [ "${section_flags:$i:1}" = "0" ]; then
            log_warn "Missing optional section: ${sections[$i]}"
        fi
    done

    # Validate workers section values (only if section exists)
    if [ "${section_flags:0:1}" = "1" ]; then
        if [ "$max_iter" -lt 1 ] || [ "$max_iter" -gt 100 ]; then
            log_error "workers.max_iterations must be between 1 and 100 (got: $max_iter)"
            ((++errors))
        fi
        if [ "$sleep_sec" -lt 0 ] || [ "$sleep_sec" -gt 60 ]; then
            log_error "workers.sleep_seconds must be between 0 and 60 (got: $sleep_sec)"
            ((++errors))
        fi
    fi

    # Validate hooks section (only if section exists)
    if [ "${section_flags:1:1}" = "1" ]; then
        if [ "$hooks_enabled" != "true" ] && [ "$hooks_enabled" != "false" ]; then
            log_error "hooks.enabled must be boolean (got: $hooks_enabled)"
            ((++errors))
        fi
    fi

    # Validate review section (only if section exists)
    if [ "${section_flags:3:1}" = "1" ]; then
        if [ "$fix_max_iter" -lt 1 ] || [ "$fix_max_iter" -gt 50 ]; then
            log_error "review.fix_max_iterations must be between 1 and 50 (got: $fix_max_iter)"
            ((++errors))
        fi
        if [ "$fix_max_turns" -lt 1 ] || [ "$fix_max_turns" -gt 100 ]; then
            log_error "review.fix_max_turns must be between 1 and 100 (got: $fix_max_turns)"
            ((++errors))
        fi
        # Validate approved_user_ids is an array if present
        if [ "$approved_type" != "null" ] && [ "$approved_type" != "array" ]; then
            log_error "review.approved_user_ids must be an array"
            ((++errors))
        fi
    fi

    # Check for unknown top-level keys
    local known_keys=("workers" "hooks" "paths" "review" "github")
    local key
    IFS=',' read -ra key_array <<< "$actual_keys"
    for key in "${key_array[@]}"; do
        local found=false
        local known
        for known in "${known_keys[@]}"; do
            if [ "$key" = "$known" ]; then
                found=true
                break
            fi
        done
        if [ "$found" = false ]; then
            log_warn "Unknown config key: $key (will be ignored)"
        fi
    done

    if [ $errors -gt 0 ]; then
        log_error "Config validation failed with $errors error(s)"
        return 1
    fi

    log_debug "Config validation passed: $config_file"
    return 0
}

# Validate agents.json against schema
#
# Args:
#   agents_file - Path to agents.json (defaults to $WIGGUM_HOME/config/agents.json)
#
# Returns: 0 if valid, 1 if invalid
# shellcheck disable=SC2120
validate_agents_config() {
    local agents_file="${1:-$WIGGUM_HOME/config/agents.json}"
    local errors=0

    log_debug "Validating agents config: $agents_file"

    # First check JSON is valid
    if ! validate_json_file "$agents_file"; then
        return 1
    fi

    # Single jq call to check required sections and get agent names (performance optimization)
    # Output format: has_agents|has_defaults|agent_names (comma-separated)
    local extracted
    extracted=$(jq -r '
        [
            (if .agents then "1" else "0" end),
            (if .defaults then "1" else "0" end),
            (.agents | keys | join(","))
        ] | join("\u001e")
    ' "$agents_file" 2>/dev/null)

    if [ -z "$extracted" ]; then
        log_error "Failed to parse agents config: $agents_file"
        return 1
    fi

    # Parse extracted values
    local has_agents has_defaults agent_names_csv
    IFS=$'\x1e' read -r has_agents has_defaults agent_names_csv <<< "$extracted"

    # Check required sections exist
    if [ "$has_agents" = "0" ]; then
        log_error "Missing required section: agents"
        ((++errors))
    fi

    if [ "$has_defaults" = "0" ]; then
        log_error "Missing required section: defaults"
        ((++errors))
    fi

    # Validate each agent definition (split CSV by comma)
    local agent_name
    IFS=',' read -ra agent_names <<< "$agent_names_csv"
    for agent_name in "${agent_names[@]}"; do
        [ -z "$agent_name" ] && continue

        # Validate agent name format
        if ! [[ "$agent_name" =~ ^[a-z][a-z0-9.-]*$ ]]; then
            log_error "Invalid agent name: '$agent_name' (must be lowercase with hyphens and dots)"
            ((++errors))
            continue
        fi

        # Validate agent parameters
        _validate_agent_params "$agents_file" ".agents[\"$agent_name\"]" "$agent_name" || ((++errors))
    done

    # Validate defaults section
    _validate_agent_params "$agents_file" ".defaults" "defaults" || ((++errors))

    if [ $errors -gt 0 ]; then
        log_error "Agents config validation failed with $errors error(s)"
        return 1
    fi

    log_debug "Agents config validation passed: $agents_file"
    return 0
}

# Internal: Validate agent parameter values
#
# Args:
#   file    - JSON file path
#   path    - jq path to agent config
#   name    - Display name for error messages
#
# Returns: 0 if valid, 1 if invalid
_validate_agent_params() {
    local file="$1"
    local path="$2"
    local name="$3"
    local errors=0

    # Single jq call extracts all parameter values at once (performance optimization)
    # Output format: max_iter|max_turns|timeout|interval|restarts|auto_commit
    local extracted
    extracted=$(jq -r "
        [
            ($path.max_iterations // \"null\"),
            ($path.max_turns // \"null\"),
            ($path.timeout_seconds // \"null\"),
            ($path.supervisor_interval // \"null\"),
            ($path.max_restarts // \"null\"),
            ($path.auto_commit // \"null\")
        ] | join(\"\u001e\")
    " "$file" 2>/dev/null)

    if [ -z "$extracted" ]; then
        # Path doesn't exist or extraction failed, nothing to validate
        return 0
    fi

    # Parse extracted values
    local max_iter max_turns timeout interval restarts auto_commit
    IFS=$'\x1e' read -r max_iter max_turns timeout interval restarts auto_commit <<< "$extracted"

    # Check max_iterations
    if [ "$max_iter" != "null" ]; then
        if ! [[ "$max_iter" =~ ^[0-9]+$ ]] || [ "$max_iter" -lt 1 ] || [ "$max_iter" -gt 100 ]; then
            log_error "$name: max_iterations must be between 1 and 100 (got: $max_iter)"
            ((++errors))
        fi
    fi

    # Check max_turns
    if [ "$max_turns" != "null" ]; then
        if ! [[ "$max_turns" =~ ^[0-9]+$ ]] || [ "$max_turns" -lt 1 ] || [ "$max_turns" -gt 200 ]; then
            log_error "$name: max_turns must be between 1 and 200 (got: $max_turns)"
            ((++errors))
        fi
    fi

    # Check timeout_seconds
    if [ "$timeout" != "null" ]; then
        if ! [[ "$timeout" =~ ^[0-9]+$ ]] || [ "$timeout" -lt 60 ] || [ "$timeout" -gt 86400 ]; then
            log_error "$name: timeout_seconds must be between 60 and 86400 (got: $timeout)"
            ((++errors))
        fi
    fi

    # Check supervisor_interval
    if [ "$interval" != "null" ]; then
        if ! [[ "$interval" =~ ^[0-9]+$ ]] || [ "$interval" -lt 1 ] || [ "$interval" -gt 20 ]; then
            log_error "$name: supervisor_interval must be between 1 and 20 (got: $interval)"
            ((++errors))
        fi
    fi

    # Check max_restarts
    if [ "$restarts" != "null" ]; then
        if ! [[ "$restarts" =~ ^[0-9]+$ ]] || [ "$restarts" -gt 10 ]; then
            log_error "$name: max_restarts must be between 0 and 10 (got: $restarts)"
            ((++errors))
        fi
    fi

    # Check auto_commit is boolean
    if [ "$auto_commit" != "null" ] && [ "$auto_commit" != "true" ] && [ "$auto_commit" != "false" ]; then
        log_error "$name: auto_commit must be boolean (got: $auto_commit)"
        ((++errors))
    fi

    return $errors
}

# Validate all configuration files
#
# Returns: 0 if all valid, 1 if any invalid
validate_all_config() {
    local errors=0

    log_info "Validating configuration files..."

    if ! validate_config; then
        ((++errors))
    fi

    if ! validate_agents_config; then
        ((++errors))
    fi

    if [ $errors -gt 0 ]; then
        log_error "Configuration validation failed"
        return 1
    fi

    log_info "All configuration files valid"
    return 0
}
