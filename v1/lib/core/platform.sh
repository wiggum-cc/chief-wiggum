#!/usr/bin/env bash
# platform.sh - Platform-specific compatibility helpers
#
# Provides portable implementations of commands that differ between
# GNU (Linux) and BSD (macOS) systems.
#
# Source this file when you need: find_newest, find_oldest, grep_pcre_match, etc.
set -euo pipefail

# =============================================================================
# PLATFORM DETECTION (cached at source time)
# =============================================================================

# Detect GNU find (supports -printf) vs BSD find (macOS)
if find . -maxdepth 0 -printf '' 2>/dev/null; then
    _FIND_HAS_PRINTF=1
else
    _FIND_HAS_PRINTF=0
fi

# =============================================================================
# PORTABLE SED
# =============================================================================

# Portable sed in-place edit (works on both GNU sed and BSD sed on macOS)
# Usage: sed_inplace <sed_expression> <file>
# Example: sed_inplace 's/foo/bar/' myfile.txt
sed_inplace() {
    if [[ "$OSTYPE" == darwin* ]]; then
        sed -i '' "$@"
    else
        sed -i "$@"
    fi
}

# =============================================================================
# PORTABLE FIND (mtime sorting)
# =============================================================================

# Portable find newest/oldest file by mtime (works on GNU and BSD find)
# Usage: find_newest <find_args...>
# Usage: find_oldest <find_args...>
# Example: find_newest "$dir" -name "*.log"
# Returns: Path to the newest/oldest file, or empty string if none found
#
# Note: On GNU find, uses -printf for efficiency. On BSD (macOS), falls back to ls -t.
find_newest() {
    if [ "$_FIND_HAS_PRINTF" = "1" ]; then
        # GNU find: use -printf for mtime sorting
        find "$@" -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-
    else
        # BSD find (macOS): use ls -t for mtime sorting
        # shellcheck disable=SC2012
        find "$@" -print0 2>/dev/null | xargs -0 ls -dt 2>/dev/null | head -1
    fi
}

find_oldest() {
    if [ "$_FIND_HAS_PRINTF" = "1" ]; then
        # GNU find: use -printf for mtime sorting
        find "$@" -printf '%T@ %p\n' 2>/dev/null | sort -n | head -1 | cut -d' ' -f2-
    else
        # BSD find (macOS): use ls -tr for mtime sorting (oldest first)
        # shellcheck disable=SC2012
        find "$@" -print0 2>/dev/null | xargs -0 ls -dtr 2>/dev/null | head -1
    fi
}

# List all matching files sorted by mtime (oldest first)
# Usage: find_sorted_by_mtime <find_args...>
# Returns: One file path per line, oldest first
find_sorted_by_mtime() {
    if [ "$_FIND_HAS_PRINTF" = "1" ]; then
        # GNU find: use -printf for mtime sorting
        find "$@" -printf '%T@ %p\n' 2>/dev/null | sort -n | cut -d' ' -f2-
    else
        # BSD find (macOS): use ls -tr for mtime sorting
        # shellcheck disable=SC2012
        find "$@" -print0 2>/dev/null | xargs -0 ls -dtr 2>/dev/null
    fi
}

# =============================================================================
# PORTABLE TIME (avoids external `date` binary where possible)
# =============================================================================

# Detect printf %()T support (bash 4.2+, avoids date subprocess)
# macOS ships bash 3.2 which does NOT support this.
_PLATFORM_HAS_PRINTF_T=0
if printf '%(%s)T' -1 &>/dev/null; then
    _PLATFORM_HAS_PRINTF_T=1
fi

# Detect GNU vs BSD date (cached — platform never changes mid-run)
# gnu: supports `date -d "@epoch"` (Linux)
# bsd: supports `date -r epoch` (macOS)
_DATE_FLAVOR="unknown"
if date -d "@0" +%s &>/dev/null 2>&1; then
    _DATE_FLAVOR="gnu"
elif date -r 0 +%s &>/dev/null 2>&1; then
    _DATE_FLAVOR="bsd"
fi

# Get cached epoch seconds for the current orchestrator tick
#
# Returns $_ORCH_TICK_EPOCH if set (avoids repeated syscalls within a single
# main-loop iteration), otherwise falls back to epoch_now().
#
# Returns: epoch seconds on stdout
epoch_tick() {
    if [[ -n "${_ORCH_TICK_EPOCH:-}" ]]; then
        echo "$_ORCH_TICK_EPOCH"
    else
        epoch_now
    fi
}

# Get current epoch seconds
#
# Uses bash built-in printf %()T when available (Linux bash 4.2+),
# falls back to external `date` command (macOS, older bash).
#
# Returns: epoch seconds on stdout
epoch_now() {
    if (( _PLATFORM_HAS_PRINTF_T )); then
        printf '%(%s)T' -1
    else
        date +%s
    fi
}

# Get current ISO 8601 timestamp (second precision with timezone offset)
#
# Uses bash built-in printf %()T when available, falls back to `date -Iseconds`.
# Note: printf produces +0000 format; date -Iseconds produces +00:00 format.
# Both are valid ISO 8601.
#
# Returns: ISO 8601 timestamp on stdout (e.g., "2024-01-26T10:30:00+0000")
iso_now() {
    if (( _PLATFORM_HAS_PRINTF_T )); then
        printf '%(%Y-%m-%dT%H:%M:%S%z)T' -1
    else
        date -Iseconds
    fi
}

# Convert epoch seconds to ISO 8601 timestamp
#
# Uses bash built-in printf %()T when available, falls back to
# GNU `date -d` or BSD `date -r`.
#
# Args:
#   epoch - Epoch seconds to convert
#
# Returns: ISO 8601 timestamp on stdout, or current time on failure
iso_from_epoch() {
    local epoch="$1"
    if (( _PLATFORM_HAS_PRINTF_T )); then
        printf '%(%Y-%m-%dT%H:%M:%S%z)T' "$epoch"
    elif [[ "$_DATE_FLAVOR" == "gnu" ]]; then
        date -Iseconds -d "@$epoch"
    elif [[ "$_DATE_FLAVOR" == "bsd" ]]; then
        date -Iseconds -r "$epoch"
    else
        date -Iseconds
    fi
}

# =============================================================================
# PORTABLE DATE (parsing and formatting)
# =============================================================================

# Parse a date string or epoch timestamp to epoch seconds
# Works on both GNU (Linux) and BSD (macOS) date commands
#
# Usage: date_parse_epoch <date_string_or_epoch>
# Examples:
#   date_parse_epoch "2024-01-26"           -> epoch
#   date_parse_epoch "2024-01-26T10:30:00"  -> epoch
#   date_parse_epoch "@1706270400"          -> 1706270400
#   date_parse_epoch "1706270400"           -> 1706270400 (if numeric)
#
# Returns: epoch timestamp on stdout, or empty on failure
date_parse_epoch() {
    local input="$1"

    # If already an epoch timestamp (numeric), return as-is
    if [[ "$input" =~ ^@?[0-9]+$ ]]; then
        echo "${input#@}"
        return 0
    fi

    if [[ "$_DATE_FLAVOR" == "gnu" ]]; then
        date -d "$input" +%s
    elif [[ "$_DATE_FLAVOR" == "bsd" ]]; then
        local epoch
        for fmt in "%Y-%m-%d" "%Y-%m-%dT%H:%M:%S" "%Y-%m-%d %H:%M:%S"; do
            epoch=$(date -j -f "$fmt" "$input" +%s 2>/dev/null) && { echo "$epoch"; return 0; }
        done
        return 1
    else
        return 1
    fi
}

# Format an epoch timestamp to a date string
# Works on both GNU (Linux) and BSD (macOS) date commands
#
# Usage: date_format_epoch <epoch> <format>
# Examples:
#   date_format_epoch 1706270400 "%Y-%m-%d"       -> "2024-01-26"
#   date_format_epoch 1706270400 "%H:%M:%S"       -> "10:30:00"
#   date_format_epoch 1706270400 "%Y-%m-%dT%H:%M:%S" -> "2024-01-26T10:30:00"
#
# Returns: formatted date string on stdout
date_format_epoch() {
    local epoch="$1"
    local format="$2"

    if (( _PLATFORM_HAS_PRINTF_T )); then
        printf "%($format)T" "$epoch"
    elif [[ "$_DATE_FLAVOR" == "gnu" ]]; then
        date -d "@$epoch" +"$format"
    elif [[ "$_DATE_FLAVOR" == "bsd" ]]; then
        date -r "$epoch" +"$format"
    else
        return 1
    fi
}

# Get today's midnight as epoch timestamp
# Works on both GNU (Linux) and BSD (macOS)
#
# Usage: date_today_midnight
# Returns: epoch timestamp for midnight today
date_today_midnight() {
    if (( _PLATFORM_HAS_PRINTF_T )); then
        # Calculate using bash built-in printf (no external date needed)
        local now hour min sec
        printf -v now '%(%s)T' -1
        printf -v hour '%(%H)T' -1
        printf -v min '%(%M)T' -1
        printf -v sec '%(%S)T' -1
        hour=$((10#$hour))
        min=$((10#$min))
        sec=$((10#$sec))
        echo $(( now - (hour * 3600) - (min * 60) - sec ))
        return 0
    fi

    local today
    today=$(date +%Y-%m-%d)

    if [[ "$_DATE_FLAVOR" == "gnu" ]]; then
        date -d "$today" +%s
    elif [[ "$_DATE_FLAVOR" == "bsd" ]]; then
        date -j -f "%Y-%m-%d" "$today" +%s
    else
        # Fallback: calculate manually
        local now hour min sec
        now=$(date +%s)
        hour=$(date +%H)
        min=$(date +%M)
        sec=$(date +%S)
        hour=$((10#$hour))
        min=$((10#$min))
        sec=$((10#$sec))
        echo $(( now - (hour * 3600) - (min * 60) - sec ))
    fi
}

# =============================================================================
# PORTABLE GREP (Perl regex)
# =============================================================================

# Portable grep with Perl regex (works on GNU grep and macOS via perl)
# Usage: grep_pcre_match <pattern> [file]
# Equivalent to: grep -oP <pattern> [file]
# Returns: matching portions only, one per line
grep_pcre_match() {
    local pattern="$1"
    local file="${2:-}"
    if [[ "$OSTYPE" == darwin* ]]; then
        # macOS: use perl since grep doesn't support -P
        if [ -n "$file" ]; then
            perl -ne 'while (m{'"$pattern"'}g) { print "$&\n"; }' "$file" 2>/dev/null
        else
            perl -ne 'while (m{'"$pattern"'}g) { print "$&\n"; }' 2>/dev/null
        fi
    else
        # Linux: use native grep -oP
        if [ -n "$file" ]; then
            grep -oP "$pattern" "$file" 2>/dev/null
        else
            grep -oP "$pattern" 2>/dev/null
        fi
    fi
}

# Portable grep -qP equivalent (quiet test for Perl regex match)
# Usage: grep_pcre_test <pattern> [file]
# Returns: 0 if match found, 1 otherwise
grep_pcre_test() {
    local pattern="$1"
    local file="${2:-}"
    if [[ "$OSTYPE" == darwin* ]]; then
        # macOS: use perl since grep doesn't support -P
        if [ -n "$file" ]; then
            perl -ne 'exit 0 if m{'"$pattern"'}' "$file" 2>/dev/null && return 0
        else
            perl -ne 'exit 0 if m{'"$pattern"'}' 2>/dev/null && return 0
        fi
        return 1
    else
        # Linux: use native grep -qP
        if [ -n "$file" ]; then
            grep -qP "$pattern" "$file" 2>/dev/null
        else
            grep -qP "$pattern" 2>/dev/null
        fi
    fi
}
