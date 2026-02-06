#!/usr/bin/env bash
# atomic-write.sh - Atomic file write via mktemp + mv
#
# Two modes:
#   Command mode: atomic_write "$target" jq -n '...'
#   Pipe mode:    echo '{}' | atomic_write "$target"
#
# Creates temp file adjacent to target (same FS for atomic mv).
# Cleans up on failure.
set -euo pipefail

[ -n "${_ATOMIC_WRITE_LOADED:-}" ] && return 0
_ATOMIC_WRITE_LOADED=1

# Write to a file atomically using mktemp + mv
#
# In command mode, runs the given command with stdout redirected to a temp file,
# then atomically moves it to the target path.
# In pipe mode (no command args), reads stdin into a temp file, then moves.
#
# Args:
#   target_file - Destination file path
#   [command...] - Optional command whose stdout becomes the file content
#
# Returns: 0 on success, command's exit code on failure (temp file cleaned up)
atomic_write() {
    local target_file="$1"; shift
    local parent_dir
    parent_dir=$(dirname "$target_file")
    [ -d "$parent_dir" ] || mkdir -p "$parent_dir"

    local tmp_file
    tmp_file=$(mktemp "${target_file}.XXXXXX")

    if [ $# -gt 0 ]; then
        # Command mode
        local rc=0
        "$@" > "$tmp_file" || rc=$?
        if [ "$rc" -eq 0 ]; then
            mv "$tmp_file" "$target_file"
        else
            rm -f "$tmp_file"
            return "$rc"
        fi
    else
        # Pipe mode
        local rc=0
        cat > "$tmp_file" || rc=$?
        if [ "$rc" -eq 0 ]; then
            mv "$tmp_file" "$target_file"
        else
            rm -f "$tmp_file"
            return "$rc"
        fi
    fi
}
