#!/usr/bin/env bash
# wdoc-registry.sh - Package registry for wdoc documentation tool
#
# Manages .ralph/wdoc-packages.json with flock-protected CRUD operations.
# Registry tracks packages added via `wdoc add` with metadata about
# documentation URLs, source repos, and versions.
#
# Schema:
#   {
#     "packages": {
#       "<name>": {
#         "doc_url": "...",
#         "src_url": "...",
#         "version": "",
#         "added_at": "...",
#         "doc_fetched_at": "...",
#         "src_cloned_at": "..."
#       }
#     }
#   }
set -euo pipefail

[ -n "${_WDOC_REGISTRY_LOADED:-}" ] && return 0
_WDOC_REGISTRY_LOADED=1

source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/safe-path.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"

# Get the path to the wdoc registry file
#
# Returns: path to .ralph/wdoc-packages.json on stdout
wdoc_registry_file() {
    echo "$RALPH_DIR/wdoc-packages.json"
}

# Ensure registry file exists with empty structure
#
# Creates .ralph/wdoc-packages.json if missing.
_wdoc_registry_ensure() {
    local registry_file
    registry_file=$(wdoc_registry_file)

    if [ ! -f "$registry_file" ]; then
        if [ ! -d "$RALPH_DIR" ]; then
            log_error "RALPH_DIR does not exist: $RALPH_DIR"
            return 1
        fi
        echo '{"packages":{}}' > "$registry_file"
    fi
}

# Add a package to the registry
#
# Args:
#   name    - Package name (e.g., "textual")
#   doc_url - Documentation URL (optional, empty string if not provided)
#   src_url - Source repository URL (optional, empty string if not provided)
#
# Returns: 0 on success, 1 on error
wdoc_registry_add() {
    local name="$1"
    local doc_url="${2:-}"
    local src_url="${3:-}"

    _wdoc_registry_ensure

    local registry_file
    registry_file=$(wdoc_registry_file)
    local timestamp
    timestamp=$(iso_now)

    _WREG_NAME="$name" \
    _WREG_DOC_URL="$doc_url" \
    _WREG_SRC_URL="$src_url" \
    _WREG_TIMESTAMP="$timestamp" \
    with_file_lock "$registry_file" 5 \
        bash -c '
            set -euo pipefail
            jq --arg name "$_WREG_NAME" \
               --arg doc_url "$_WREG_DOC_URL" \
               --arg src_url "$_WREG_SRC_URL" \
               --arg ts "$_WREG_TIMESTAMP" \
               ".packages[\$name] = {
                   doc_url: \$doc_url,
                   src_url: \$src_url,
                   version: \"\",
                   added_at: \$ts,
                   doc_fetched_at: \"\",
                   src_cloned_at: \"\"
               }" "$1" > "$1.tmp" && mv "$1.tmp" "$1"
        ' _ "$registry_file"
}

# Get a package entry from the registry
#
# Args:
#   name - Package name
#
# Returns: JSON object for the package on stdout, or empty + exit 1 if not found
wdoc_registry_get() {
    local name="$1"

    _wdoc_registry_ensure

    local registry_file
    registry_file=$(wdoc_registry_file)

    [ -f "$registry_file" ] || return 1

    local result
    result=$(jq -r --arg name "$name" '.packages[$name] // empty' "$registry_file" 2>/dev/null)

    if [ -z "$result" ]; then
        return 1
    fi

    echo "$result"
}

# List all packages in the registry
#
# Returns: tab-separated lines of "name\tversion\tdoc_url\tsrc_url" on stdout
#          Empty output if no packages registered.
wdoc_registry_list() {
    _wdoc_registry_ensure

    local registry_file
    registry_file=$(wdoc_registry_file)

    [ -f "$registry_file" ] || return 0

    jq -r '.packages | to_entries[] | [.key, .value.version, .value.doc_url, .value.src_url] | join("\u001e")' \
        "$registry_file" 2>/dev/null
}

# Remove a package from the registry
#
# Args:
#   name - Package name to remove
#
# Returns: 0 on success, 1 if not found
wdoc_registry_remove() {
    local name="$1"

    _wdoc_registry_ensure

    local registry_file
    registry_file=$(wdoc_registry_file)

    # Check existence first
    if ! jq -e --arg name "$name" '.packages[$name] != null' "$registry_file" > /dev/null 2>&1; then
        return 1
    fi

    _WREG_NAME="$name" \
    with_file_lock "$registry_file" 5 \
        bash -c '
            set -euo pipefail
            jq --arg name "$_WREG_NAME" "del(.packages[\$name])" "$1" > "$1.tmp" && mv "$1.tmp" "$1"
        ' _ "$registry_file"
}

# Set the version field for a package
#
# Args:
#   name    - Package name
#   version - Version string (e.g., "3.2.0")
#
# Returns: 0 on success, 1 if package not found
wdoc_registry_set_version() {
    local name="$1"
    local version="$2"

    _wdoc_registry_ensure

    local registry_file
    registry_file=$(wdoc_registry_file)

    # Check existence first
    if ! jq -e --arg name "$name" '.packages[$name] != null' "$registry_file" > /dev/null 2>&1; then
        return 1
    fi

    _WREG_NAME="$name" \
    _WREG_VERSION="$version" \
    with_file_lock "$registry_file" 5 \
        bash -c '
            set -euo pipefail
            jq --arg name "$_WREG_NAME" \
               --arg ver "$_WREG_VERSION" \
               ".packages[\$name].version = \$ver" "$1" > "$1.tmp" && mv "$1.tmp" "$1"
        ' _ "$registry_file"
}

# Update a timestamp field for a package
#
# Args:
#   name  - Package name
#   field - Field name (doc_fetched_at or src_cloned_at)
#
# Returns: 0 on success, 1 if package not found
wdoc_registry_set_timestamp() {
    local name="$1"
    local field="$2"

    _wdoc_registry_ensure

    local registry_file
    registry_file=$(wdoc_registry_file)
    local timestamp
    timestamp=$(iso_now)

    # Check existence first
    if ! jq -e --arg name "$name" '.packages[$name] != null' "$registry_file" > /dev/null 2>&1; then
        return 1
    fi

    _WREG_NAME="$name" \
    _WREG_FIELD="$field" \
    _WREG_TS="$timestamp" \
    with_file_lock "$registry_file" 5 \
        bash -c '
            set -euo pipefail
            jq --arg name "$_WREG_NAME" \
               --arg field "$_WREG_FIELD" \
               --arg ts "$_WREG_TS" \
               ".packages[\$name][\$field] = \$ts" "$1" > "$1.tmp" && mv "$1.tmp" "$1"
        ' _ "$registry_file"
}
