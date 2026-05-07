#!/usr/bin/env bash
# =============================================================================
# arg-parser.sh - Parse wiggum-run CLI arguments
#
# Extracted from wiggum-run main() to keep the orchestrator script lean.
#
# Provides:
#   _parse_run_args()  - Parse CLI arguments, set global config variables
# =============================================================================
set -euo pipefail

[ -n "${_ORCHESTRATOR_ARG_PARSER_LOADED:-}" ] && return 0
_ORCHESTRATOR_ARG_PARSER_LOADED=1

# Parse wiggum run CLI arguments
#
# Sets global variables:
#   MAX_WORKERS, MAX_ITERATIONS, MAX_TURNS, WIGGUM_RUN_MODE,
#   WIGGUM_PLAN_MODE, WIGGUM_SMART_MODE (default: true), WIGGUM_PIPELINE,
#   FIX_WORKER_LIMIT, FORCE_LOCK, WIGGUM_USE_PYTHON (default: true),
#   WIGGUM_NO_RESUME, WIGGUM_NO_FIX, WIGGUM_NO_MERGE, WIGGUM_NO_SYNC, WIGGUM_SKIP_REVIEW,
#   WIGGUM_TASK_SOURCE_MODE (default: hybrid), WIGGUM_SERVER_ID
#
# Args:
#   "$@" - Command line arguments (after verbose flags removed)
_parse_run_args() {
    while [[ $# -gt 0 ]]; do
        case "$1" in
            plan|--plan)
                export WIGGUM_PLAN_MODE=true
                shift
                ;;
            --smart)
                # No-op: smart mode is now the default
                shift
                ;;
            --fix-only)
                WIGGUM_RUN_MODE="fix-only"
                shift
                ;;
            --merge-only)
                WIGGUM_RUN_MODE="merge-only"
                shift
                ;;
            --resume-only)
                WIGGUM_RUN_MODE="resume-only"
                shift
                ;;
            --max-workers)
                if [[ -z "${2:-}" ]] || [[ "${2:-}" =~ ^- ]]; then
                    echo "Error: --max-workers requires a number argument"
                    exit $EXIT_USAGE
                fi
                # shellcheck disable=SC2034
                MAX_WORKERS="$2"
                shift 2
                ;;
            --max-iters)
                if [[ -z "${2:-}" ]] || [[ "${2:-}" =~ ^- ]]; then
                    echo "Error: --max-iters requires a number argument"
                    exit $EXIT_USAGE
                fi
                # shellcheck disable=SC2034
                MAX_ITERATIONS="$2"
                shift 2
                ;;
            --max-turns)
                if [[ -z "${2:-}" ]] || [[ "${2:-}" =~ ^- ]]; then
                    echo "Error: --max-turns requires a number argument"
                    exit $EXIT_USAGE
                fi
                # shellcheck disable=SC2034
                MAX_TURNS="$2"
                shift 2
                ;;
            --fix-agents)
                if [[ -z "${2:-}" ]] || [[ "${2:-}" =~ ^- ]]; then
                    echo "Error: --fix-agents requires a number argument"
                    exit $EXIT_USAGE
                fi
                # shellcheck disable=SC2034
                FIX_WORKER_LIMIT="$2"
                shift 2
                ;;
            --pipeline)
                if [[ -z "${2:-}" ]] || [[ "${2:-}" =~ ^- ]]; then
                    echo "Error: --pipeline requires a name argument"
                    exit $EXIT_USAGE
                fi
                export WIGGUM_PIPELINE="$2"
                shift 2
                ;;
            --mode)
                if [[ -z "${2:-}" ]] || [[ "${2:-}" =~ ^- ]]; then
                    echo "Error: --mode requires an argument (local, github, or hybrid)"
                    exit $EXIT_USAGE
                fi
                case "$2" in
                    local|github|hybrid)
                        export WIGGUM_TASK_SOURCE_MODE="$2"
                        ;;
                    *)
                        echo "Error: --mode must be one of: local, github, hybrid"
                        exit $EXIT_USAGE
                        ;;
                esac
                shift 2
                ;;
            --server-id)
                if [[ -z "${2:-}" ]] || [[ "${2:-}" =~ ^- ]]; then
                    echo "Error: --server-id requires a server identifier"
                    exit $EXIT_USAGE
                fi
                export WIGGUM_SERVER_ID="$2"
                shift 2
                ;;
            --no-resume)
                # shellcheck disable=SC2034
                WIGGUM_NO_RESUME=true
                shift
                ;;
            --no-fix)
                # shellcheck disable=SC2034
                WIGGUM_NO_FIX=true
                shift
                ;;
            --no-merge)
                # shellcheck disable=SC2034
                WIGGUM_NO_MERGE=true
                shift
                ;;
            --no-sync)
                # shellcheck disable=SC2034
                WIGGUM_NO_SYNC=true
                shift
                ;;
            --skip-review)
                # shellcheck disable=SC2034
                WIGGUM_SKIP_REVIEW=true
                shift
                ;;
            --python)
                # No-op: Python scheduler is now the default
                shift
                ;;
            --no-python)
                # shellcheck disable=SC2034
                WIGGUM_USE_PYTHON=false
                shift
                ;;
            --force)
                # shellcheck disable=SC2034
                FORCE_LOCK=true
                shift
                ;;
            -h|--help)
                show_help
                exit $EXIT_OK
                ;;
            -*)
                echo "Unknown option: $1"
                echo ""
                show_help
                exit $EXIT_USAGE
                ;;
            *)
                echo "Unknown argument: $1"
                echo ""
                show_help
                exit $EXIT_USAGE
                ;;
        esac
    done

    # Validate mutually exclusive options
    if [[ "$WIGGUM_RUN_MODE" != "default" && "${WIGGUM_PLAN_MODE:-false}" == "true" ]]; then
        echo "Error: --${WIGGUM_RUN_MODE} cannot be combined with --plan"
        exit $EXIT_USAGE
    fi
    # Smart mode (default) is incompatible with explicit plan/pipeline/run-mode
    # overrides. Silently disable it when these are set.
    if [[ "${WIGGUM_SMART_MODE:-true}" == "true" ]]; then
        if [[ "${WIGGUM_PLAN_MODE:-false}" == "true" ]] \
            || [[ -n "${WIGGUM_PIPELINE:-}" ]] \
            || [[ "$WIGGUM_RUN_MODE" != "default" ]]; then
            WIGGUM_SMART_MODE=false
        fi
    fi

    # Validate --no-* flags don't contradict --*-only modes
    if [[ "${WIGGUM_NO_RESUME:-false}" == "true" && "$WIGGUM_RUN_MODE" == "resume-only" ]]; then
        echo "Error: --no-resume cannot be combined with --resume-only"
        exit $EXIT_USAGE
    fi
    if [[ "${WIGGUM_NO_FIX:-false}" == "true" && "$WIGGUM_RUN_MODE" == "fix-only" ]]; then
        echo "Error: --no-fix cannot be combined with --fix-only"
        exit $EXIT_USAGE
    fi
    if [[ "${WIGGUM_NO_MERGE:-false}" == "true" && "$WIGGUM_RUN_MODE" == "merge-only" ]]; then
        echo "Error: --no-merge cannot be combined with --merge-only"
        exit $EXIT_USAGE
    fi
}
