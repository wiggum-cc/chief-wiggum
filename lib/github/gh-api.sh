#!/usr/bin/env bash
# gh-api.sh - Consolidated GitHub API wrapper
#
# Provides unified interface for GitHub CLI operations with:
# - Timeout handling
# - Network error retry with backoff
# - Consistent error logging
# - Safe defaults (return empty on failure)
set -euo pipefail

[ -n "${_GH_API_LOADED:-}" ] && return 0
_GH_API_LOADED=1

[ -z "${_WIGGUM_SRC_LOGGER_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/gh-error.sh"

# Configuration
WIGGUM_GH_TIMEOUT="${WIGGUM_GH_TIMEOUT:-30}"
WIGGUM_GH_RETRIES="${WIGGUM_GH_RETRIES:-2}"
WIGGUM_GH_RETRY_DELAY="${WIGGUM_GH_RETRY_DELAY:-2}"
# Rate limit minimum: env var > config.json > default
if [ -z "${WIGGUM_GH_RATE_LIMIT_MIN:-}" ]; then
    WIGGUM_GH_RATE_LIMIT_MIN=$(jq -r '.github.rate_limit.min_remaining // empty' "${WIGGUM_HOME}/config/config.json" 2>/dev/null) || true
fi
WIGGUM_GH_RATE_LIMIT_MIN="${WIGGUM_GH_RATE_LIMIT_MIN:-100}"

# Check GitHub API rate limit and wait if remaining is below threshold
#
# Queries the GitHub rate_limit API and pauses execution if remaining
# requests are below the configured minimum. Waits until the reset time.
#
# Args:
#   min_remaining - Override minimum remaining threshold (optional)
#
# Returns:
#   0 if OK to proceed (rate limit sufficient or check failed gracefully)
#   1 if rate limited and waited for reset
gh_rate_limit_guard() {
    local min_remaining="${1:-$WIGGUM_GH_RATE_LIMIT_MIN}"

    local rate_json exit_code=0
    rate_json=$(timeout 10 gh api rate_limit 2>/dev/null) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_debug "gh_rate_limit_guard: Could not check rate limit (exit $exit_code)"
        return 0  # Proceed if we can't check
    fi

    local remaining reset_at
    remaining=$(echo "$rate_json" | jq '.resources.core.remaining // -1' 2>/dev/null)
    remaining="${remaining:--1}"
    reset_at=$(echo "$rate_json" | jq '.resources.core.reset // 0' 2>/dev/null)
    reset_at="${reset_at:-0}"

    if [ "$remaining" -ge 0 ] && [ "$remaining" -lt "$min_remaining" ]; then
        local now wait_seconds
        now=$(date +%s)
        wait_seconds=$(( reset_at - now + 5 ))  # +5s buffer

        if [ "$wait_seconds" -gt 0 ] && [ "$wait_seconds" -lt 3700 ]; then
            log_warn "GitHub API rate limit low ($remaining remaining, min=$min_remaining). Waiting ${wait_seconds}s for reset."
            sleep "$wait_seconds"
        elif [ "$wait_seconds" -le 0 ]; then
            log_debug "gh_rate_limit_guard: Rate limit low but reset imminent"
        else
            log_warn "GitHub API rate limit low ($remaining remaining) but reset too far away (${wait_seconds}s). Proceeding anyway."
            return 0
        fi
        return 1
    fi

    log_debug "gh_rate_limit_guard: OK ($remaining remaining)"
    return 0
}

# Get rate limit wait time from an API error response
#
# Extracts Retry-After or calculates wait from X-RateLimit-Reset if present.
# Falls back to a default wait time.
#
# Args:
#   output - Error output from gh command
#
# Returns: Wait seconds on stdout
_gh_rate_limit_wait_seconds() {
    local output="${1:-}"

    # Try to extract reset time from gh api rate_limit
    local rate_json exit_code=0
    rate_json=$(timeout 10 gh api rate_limit 2>/dev/null) || exit_code=$?

    if [ "$exit_code" -eq 0 ]; then
        local reset_at
        reset_at=$(echo "$rate_json" | jq '.resources.core.reset // 0' 2>/dev/null)
        reset_at="${reset_at:-0}"

        if [ "$reset_at" -gt 0 ]; then
            local now wait
            now=$(date +%s)
            wait=$(( reset_at - now + 5 ))
            if [ "$wait" -gt 0 ] && [ "$wait" -lt 3700 ]; then
                echo "$wait"
                return
            fi
        fi
    fi

    # Default: wait 60 seconds
    echo "60"
}

# Execute gh api with timeout, retry, and error handling
#
# Args:
#   endpoint    - API endpoint (e.g., "repos/owner/repo/pulls/123")
#   jq_filter   - Optional jq filter (default: ".")
#   method      - HTTP method (default: GET)
#
# Returns:
#   0 on success, 1 on failure
#   JSON result on success, "[]" or "{}" on failure
gh_api() {
    local endpoint="$1"
    local jq_filter="${2:-.}"
    local method="${3:-GET}"
    local timeout="${WIGGUM_GH_TIMEOUT}"
    local max_retries="${WIGGUM_GH_RETRIES}"

    local attempt=0
    local result exit_code

    while [ "$attempt" -le "$max_retries" ]; do
        exit_code=0
        result=$(timeout "$timeout" gh api "$endpoint" -X "$method" --jq "$jq_filter" 2>&1) || exit_code=$?

        if [ "$exit_code" -eq 0 ]; then
            echo "$result"
            return 0
        fi

        # Rate limit: wait for reset then retry once
        if gh_is_rate_limit_error "$exit_code" "$result"; then
            local wait_secs
            wait_secs=$(_gh_rate_limit_wait_seconds "$result")
            log_warn "gh_api: Rate limited on $endpoint, waiting ${wait_secs}s for reset"
            sleep "$wait_secs"
            # Single retry after rate limit wait
            exit_code=0
            result=$(timeout "$timeout" gh api "$endpoint" -X "$method" --jq "$jq_filter" 2>&1) || exit_code=$?
            if [ "$exit_code" -eq 0 ]; then
                echo "$result"
                return 0
            fi
            break
        fi

        # Check if retryable (network errors)
        if gh_is_network_error "$exit_code" "$result"; then
            ((++attempt))
            if [ "$attempt" -le "$max_retries" ]; then
                local delay=$((WIGGUM_GH_RETRY_DELAY * attempt))
                log_debug "gh_api: Network error, retry $attempt/$max_retries in ${delay}s: $endpoint"
                sleep "$delay"
                continue
            fi
        fi

        # Non-retryable or exhausted retries
        break
    done

    # Log failure
    if [ "$exit_code" -eq 124 ]; then
        log_error "gh_api: Timeout after ${timeout}s: $endpoint"
    elif gh_is_rate_limit_error "$exit_code" "${result:-}"; then
        log_error "gh_api: Rate limited: $endpoint (waited but still throttled)"
    else
        log_error "gh_api: Failed (exit $exit_code): $endpoint"
        [ -n "${result:-}" ] && log_debug "gh_api: Response: $result"
    fi

    # Return empty array/object based on expected response
    if [[ "$jq_filter" == *"[]"* ]] || [[ "$endpoint" == *"/list"* ]] || [[ "$endpoint" == *"s?"* ]]; then
        echo "[]"
    else
        echo "{}"
    fi
    return 1
}

# Execute gh api for endpoints that return arrays, with pagination
#
# Args:
#   endpoint    - API endpoint
#   jq_filter   - jq filter to apply to each page
#   per_page    - Items per page (default: 100)
#
# Returns: Concatenated JSON array of all pages
gh_api_paginated() {
    local endpoint="$1"
    local jq_filter="${2:-.}"
    local per_page="${3:-100}"

    local all_results="[]"
    local page=1
    local page_results

    while true; do
        local sep="?"
        [[ "$endpoint" == *"?"* ]] && sep="&"

        page_results=$(gh_api "${endpoint}${sep}per_page=${per_page}&page=${page}" "$jq_filter") || break

        # Check if empty
        local count
        count=$(echo "$page_results" | jq 'length // 0')
        count="${count:-0}"
        [ "$count" -eq 0 ] && break

        # Merge results
        all_results=$(echo "$all_results" "$page_results" | jq -s 'add')

        # Check if last page
        [ "$count" -lt "$per_page" ] && break
        ((++page))

        # Safety limit
        if [ "$page" -gt 50 ]; then
            log_warn "gh_api_paginated: Hit page limit (50) for $endpoint"
            break
        fi
    done

    echo "$all_results"
}

# Execute gh pr list with error handling
#
# Args:
#   search_query - Search query for gh pr list
#   json_fields  - Fields to return (e.g., "number,headRefName,url")
#   state        - PR state filter (default: "open")
#   extra_args   - Additional arguments (optional)
#
# Returns: JSON array of PRs, [] on failure
gh_pr_list() {
    local search_query="$1"
    local json_fields="${2:-number,headRefName,url,state}"
    local state="${3:-open}"
    local extra_args="${4:-}"
    local timeout="${WIGGUM_GH_TIMEOUT}"
    local max_retries="${WIGGUM_GH_RETRIES}"

    local attempt=0
    local result exit_code

    while [ "$attempt" -le "$max_retries" ]; do
        exit_code=0
        # shellcheck disable=SC2086
        result=$(timeout "$timeout" gh pr list --search "$search_query" --json "$json_fields" --state "$state" $extra_args 2>&1) || exit_code=$?

        if [ "$exit_code" -eq 0 ]; then
            echo "$result"
            return 0
        fi

        # Rate limit: wait for reset then retry once
        if gh_is_rate_limit_error "$exit_code" "$result"; then
            local wait_secs
            wait_secs=$(_gh_rate_limit_wait_seconds "$result")
            log_warn "gh_pr_list: Rate limited, waiting ${wait_secs}s for reset"
            sleep "$wait_secs"
            exit_code=0
            # shellcheck disable=SC2086
            result=$(timeout "$timeout" gh pr list --search "$search_query" --json "$json_fields" --state "$state" $extra_args 2>&1) || exit_code=$?
            if [ "$exit_code" -eq 0 ]; then
                echo "$result"
                return 0
            fi
            break
        fi

        if gh_is_network_error "$exit_code" "$result"; then
            ((++attempt))
            if [ "$attempt" -le "$max_retries" ]; then
                local delay=$((WIGGUM_GH_RETRY_DELAY * attempt))
                log_debug "gh_pr_list: Network error, retry $attempt/$max_retries in ${delay}s"
                sleep "$delay"
                continue
            fi
        fi
        break
    done

    if [ "$exit_code" -eq 124 ]; then
        log_error "gh_pr_list: Timeout after ${timeout}s: $search_query"
    elif gh_is_rate_limit_error "$exit_code" "${result:-}"; then
        log_error "gh_pr_list: Rate limited: $search_query (waited but still throttled)"
    else
        log_error "gh_pr_list: Failed (exit $exit_code): $search_query"
        [ -n "${result:-}" ] && log_debug "gh_pr_list: Response: $result"
    fi

    echo "[]"
    return 1
}

# Execute GraphQL query with error handling
#
# Args:
#   query      - GraphQL query string or @file
#   variables  - JSON variables (optional)
#
# Returns: JSON result, {} on failure
gh_graphql() {
    local query="$1"
    local variables="${2:-{\}}"
    local timeout="${WIGGUM_GH_TIMEOUT}"
    local max_retries="${WIGGUM_GH_RETRIES}"

    local attempt=0
    local result exit_code
    local -a var_args=()

    # Parse variables into -F arguments
    if [ "$variables" != "{}" ]; then
        while IFS='=' read -r key value; do
            [ -n "$key" ] && var_args+=(-F "$key=$value")
        done < <(echo "$variables" | jq -r 'to_entries | .[] | "\(.key)=\(.value)"')
    fi

    while [ "$attempt" -le "$max_retries" ]; do
        exit_code=0
        if [ ${#var_args[@]} -gt 0 ]; then
            result=$(timeout "$timeout" gh api graphql -f query="$query" "${var_args[@]}" 2>&1) || exit_code=$?
        else
            result=$(timeout "$timeout" gh api graphql -f query="$query" 2>&1) || exit_code=$?
        fi

        if [ "$exit_code" -eq 0 ]; then
            echo "$result"
            return 0
        fi

        # Rate limit: wait for reset then retry once
        if gh_is_rate_limit_error "$exit_code" "$result"; then
            local wait_secs
            wait_secs=$(_gh_rate_limit_wait_seconds "$result")
            log_warn "gh_graphql: Rate limited, waiting ${wait_secs}s for reset"
            sleep "$wait_secs"
            exit_code=0
            if [ ${#var_args[@]} -gt 0 ]; then
                result=$(timeout "$timeout" gh api graphql -f query="$query" "${var_args[@]}" 2>&1) || exit_code=$?
            else
                result=$(timeout "$timeout" gh api graphql -f query="$query" 2>&1) || exit_code=$?
            fi
            if [ "$exit_code" -eq 0 ]; then
                echo "$result"
                return 0
            fi
            break
        fi

        if gh_is_network_error "$exit_code" "$result"; then
            ((++attempt))
            if [ "$attempt" -le "$max_retries" ]; then
                sleep "$((WIGGUM_GH_RETRY_DELAY * attempt))"
                continue
            fi
        fi
        break
    done

    if gh_is_rate_limit_error "$exit_code" "${result:-}"; then
        log_error "gh_graphql: Rate limited (waited but still throttled)"
    else
        log_error "gh_graphql: Failed (exit $exit_code)"
    fi
    [ -n "${result:-}" ] && log_debug "gh_graphql: Response: $result"

    echo "{}"
    return 1
}

# Get current GitHub user login
#
# Returns: GitHub username or empty string on failure
gh_current_user() {
    gh_api "user" ".login" 2>/dev/null || echo ""
}

# Get current GitHub user numeric ID
#
# Returns: GitHub user ID or empty string on failure
gh_current_user_id() {
    gh_api "user" ".id" 2>/dev/null || echo ""
}
