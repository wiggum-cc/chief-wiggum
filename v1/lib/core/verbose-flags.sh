#!/usr/bin/env bash
# Verbose flag parsing for Chief Wiggum CLI
#
# Provides unified -v, -vv, -vvv verbose flags across all wiggum commands.
# Maps to the existing LOG_LEVEL system in lib/core/logger.sh.
#
# Mapping:
#   (none)      -> INFO (default)
#   -v          -> INFO (same as default, for consistency)
#   -vv         -> DEBUG (detailed diagnostic output)
#   -vvv        -> TRACE (very detailed tracing output)
#   -q/--quiet  -> WARN (suppress info messages)
#
# Usage in subcommands:
#   source "$WIGGUM_HOME/lib/core/verbose-flags.sh"
#   parse_verbose_flags "$@"
#   set -- "${WIGGUM_REMAINING_ARGS[@]}"
#   # Now LOG_LEVEL is exported and $@ contains remaining args
set -euo pipefail

[ -n "${_VERBOSE_FLAGS_LOADED:-}" ] && return 0
_VERBOSE_FLAGS_LOADED=1

# Global array to hold remaining args after parsing
declare -a WIGGUM_REMAINING_ARGS=()

# Parse verbose flags from arguments
#
# Sets:
#   LOG_LEVEL (exported) - based on verbose flags
#   WIGGUM_REMAINING_ARGS - array of non-verbose-flag arguments
#
# Args: "$@" - all command line arguments
#
# Example:
#   parse_verbose_flags "$@"
#   set -- "${WIGGUM_REMAINING_ARGS[@]}"
parse_verbose_flags() {
    local verbose_level=0
    local quiet=false
    WIGGUM_REMAINING_ARGS=()

    while [[ $# -gt 0 ]]; do
        case "$1" in
            -vvv)
                verbose_level=3
                shift
                ;;
            -vv)
                verbose_level=2
                shift
                ;;
            -v|--verbose)
                verbose_level=1
                shift
                ;;
            -q|--quiet)
                quiet=true
                shift
                ;;
            *)
                WIGGUM_REMAINING_ARGS+=("$1")
                shift
                ;;
        esac
    done

    # Set LOG_LEVEL based on flags (quiet takes precedence)
    if [[ "$quiet" == "true" ]]; then
        export LOG_LEVEL=WARN
    elif [[ $verbose_level -ge 3 ]]; then
        export LOG_LEVEL=TRACE
    elif [[ $verbose_level -ge 2 ]]; then
        export LOG_LEVEL=DEBUG
    fi
    # Note: -v (level 1) keeps default INFO, so no change needed
}

# Show verbose flag options for help text
#
# Returns a formatted string suitable for inclusion in show_help() functions.
# Call this in the Options section of help output.
#
# Usage:
#   cat << EOF
#   Options:
#   $(verbose_flags_help)
#     -h, --help          Show this help message
#   EOF
verbose_flags_help() {
    cat << 'VERBOSE_HELP'
  -v, --verbose       Verbose output (same as default)
  -vv                 Debug output (detailed diagnostics)
  -vvv                Trace output (very detailed tracing)
  -q, --quiet         Quiet mode (warnings and errors only)
VERBOSE_HELP
}
