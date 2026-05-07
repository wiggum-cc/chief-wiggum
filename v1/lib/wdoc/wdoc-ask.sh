#!/usr/bin/env bash
# wdoc-ask.sh - Agent-powered Q&A for package documentation
#
# Launches a lightweight Claude agent to explore downloaded docs and source
# code, answering questions about a specific package. Supports resumable
# sessions for followup questions.
#
# CRITICAL: This module outputs to stdout. It must NOT call log() or
# log_info() internally — only log_debug() and log_error() (stderr).
set -euo pipefail

[ -n "${_WDOC_ASK_LOADED:-}" ] && return 0
_WDOC_ASK_LOADED=1

[ -z "${_WIGGUM_SRC_PLATFORM_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/platform.sh"
[ -z "${_WIGGUM_SRC_LOGGER_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/safe-path.sh"
source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"
source "$WIGGUM_HOME/lib/runtime/runtime.sh"

# Ask a question about a package's documentation
#
# Args:
#   name       - Package name (must be registered)
#   question   - Question to ask
#   session_id - Optional session ID for followup (empty for new session)
#
# Returns: 0 on success, prints answer + session marker to stdout
wdoc_ask() {
    local name="$1"
    local question="$2"
    local session_id="${3:-}"

    if [[ -z "$name" ]]; then
        log_error "wdoc_ask: package name required"
        return 1
    fi

    if [[ -z "$question" ]]; then
        log_error "wdoc_ask: question required"
        return 1
    fi

    # Look up package in registry
    local pkg_json
    pkg_json=$(wdoc_registry_get "$name") || {
        log_error "wdoc_ask: package '$name' not found in registry (run 'wdoc add' first)"
        return 1
    }

    local workspace="$RALPH_DIR/docs/$name"
    safe_path "$workspace" "workspace" || return 1

    if [[ ! -d "$workspace" ]]; then
        log_error "wdoc_ask: docs directory not found: $workspace"
        return 1
    fi

    # Create log directory
    local log_dir="$workspace/ask-logs"
    mkdir -p "$log_dir"

    local log_file
    log_file="$log_dir/ask-$(epoch_now)-$$.log"

    if [[ -n "$session_id" ]]; then
        _wdoc_ask_resume "$name" "$question" "$session_id" "$log_file" "$pkg_json"
    else
        _wdoc_ask_new "$name" "$question" "$log_file" "$workspace" "$pkg_json"
    fi
}

# Start a new ask session
#
# Args:
#   name      - Package name
#   question  - Question to ask
#   log_file  - Log file path
#   workspace - Docs workspace directory
#   pkg_json  - Package JSON from registry
_wdoc_ask_new() {
    local name="$1"
    local question="$2"
    local log_file="$3"
    local workspace="$4"
    local pkg_json="$5"

    # Check if version is already set
    local current_version
    current_version=$(echo "$pkg_json" | jq -r '.version // empty' 2>/dev/null)

    # Build system prompt
    local system_prompt
    system_prompt=$(_wdoc_build_system_prompt "$name" "$current_version")

    # Generate session ID
    local session_id
    session_id=$(runtime_backend_generate_session_id)

    log_debug "wdoc ask: new session $session_id for package $name"

    # Run agent
    local exit_code=0
    run_agent_once_with_session "$workspace" "$system_prompt" "$question" "$log_file" 10 "$session_id" || exit_code=$?

    if [[ "$exit_code" -ne 0 ]]; then
        log_error "wdoc ask: agent failed (exit: $exit_code)"
        return 1
    fi

    # Extract answer text
    local answer
    answer=$(runtime_backend_extract_text "$log_file")

    if [[ -z "$answer" ]]; then
        log_error "wdoc ask: no answer extracted from agent output"
        return 1
    fi

    # On first ask (no version set): extract version from agent output
    if [[ -z "$current_version" ]]; then
        local detected_version
        detected_version=$(grep -oP '<wdoc_version>\K[^<]+' "$log_file" 2>/dev/null | head -1)
        if [[ -n "$detected_version" ]]; then
            wdoc_registry_set_version "$name" "$detected_version"
            log_debug "wdoc ask: detected version $detected_version for $name"
        fi
    fi

    # Print answer and session marker to stdout
    echo "$answer"
    echo ""
    echo "[wdoc:session:$session_id]"
}

# Resume an existing session with a followup question
#
# Args:
#   name       - Package name
#   question   - Followup question
#   session_id - Session ID to resume
#   log_file   - Log file path
#   pkg_json   - Package JSON from registry
_wdoc_ask_resume() {
    local name="$1"
    local question="$2"
    local session_id="$3"
    local log_file="$4"
    local pkg_json="$5"

    log_debug "wdoc ask: resuming session $session_id for package $name"

    # Run agent resume
    local exit_code=0
    run_agent_resume "$session_id" "$question" "$log_file" 10 || exit_code=$?

    if [[ "$exit_code" -ne 0 ]]; then
        log_error "wdoc ask: agent resume failed (exit: $exit_code)"
        return 1
    fi

    # Extract answer text
    local answer
    answer=$(runtime_backend_extract_text "$log_file")

    if [[ -z "$answer" ]]; then
        log_error "wdoc ask: no answer extracted from agent output"
        return 1
    fi

    # Print answer and session marker to stdout
    echo "$answer"
    echo ""
    echo "[wdoc:session:$session_id]"
}

# Build the system prompt for the wdoc agent
#
# Args:
#   name    - Package name
#   version - Current version (empty if not yet detected)
#
# Returns: system prompt on stdout
_wdoc_build_system_prompt() {
    local name="$1"
    local version="${2:-}"

    local version_instruction=""
    if [[ -z "$version" ]]; then
        version_instruction="

IMPORTANT - Version Detection:
This is the first query for this package. Determine the package version from
the documentation or source code. Output the version on a line by itself in
this exact format: <wdoc_version>X.Y.Z</wdoc_version>
(Replace X.Y.Z with the actual version number you find.)"
    fi

    cat <<PROMPT
You are a documentation researcher for the "$name" package.

Your workspace contains downloaded documentation and/or source code:
- web/ — Markdown-converted documentation pages
- git/ — Source code repository (if available)

Instructions:
1. Read the markdown docs in web/ first to answer the question
2. If docs are insufficient, explore source code in git/
3. Answer concisely and cite source files when referencing specific code
4. Do NOT modify any files — read-only access only
5. Focus on accuracy — quote relevant code or documentation passages${version_instruction}
PROMPT
}
