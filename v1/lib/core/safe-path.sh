#!/usr/bin/env bash
# safe-path.sh - Path validation to prevent destructive ops on empty/root paths
#
# Validates that a path is non-empty, not root, and not dangerously shallow
# before filesystem operations. No logger.sh dependency — stderr only.
set -euo pipefail

[ -n "${_SAFE_PATH_LOADED:-}" ] && return 0
_SAFE_PATH_LOADED=1

# Validate a path is non-empty, not root, and not dangerously shallow.
# Call before any filesystem operation using a variable-derived path.
#
# Args:
#   path - The path to validate
#   name - (optional) Variable name for error messages
#
# Returns: 0 if valid, 1 if invalid (with error on stderr)
safe_path() {
    local path="${1:-}"
    local name="${2:-path}"

    if [[ -z "$path" || "$path" == "null" ]]; then
        echo "[FATAL] safe_path: $name is empty or null — refusing filesystem operation" >&2
        return 1
    fi
    if [[ "$path" == "/" || "$path" == "//" ]]; then
        echo "[FATAL] safe_path: $name is root — refusing filesystem operation" >&2
        return 1
    fi
    # Minimum depth: at least /a/b (2 components) for absolute paths
    if [[ "$path" == /* ]]; then
        local clean="${path%/}"
        clean="${clean#/}"
        local depth
        depth=$(echo "$clean" | awk -F'/' '{print NF}')
        if [[ "$depth" -lt 2 ]]; then
            echo "[FATAL] safe_path: $name too shallow (<2 components): $path" >&2
            return 1
        fi
    fi
    return 0
}
