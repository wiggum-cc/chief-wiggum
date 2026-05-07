#!/usr/bin/env bash
# mock-gh.sh - Mock GitHub CLI for testing
#
# Intercepts gh commands to allow:
# - Logging of invocations
# - Stateful management of issues and PRs via a JSON "database"
# - Injection of failures
#
# Environment Variables:
#   MOCK_GH_LOG_DIR       - Directory to store logs (required)
#   MOCK_GH_EXIT_CODE     - Force exit code
#   MOCK_GH_OUTPUT        - Force stdout
#   MOCK_GH_SCENARIO      - Activate a specific scenario logic
#   MOCK_GH_DB            - Path to JSON database (default: $MOCK_GH_LOG_DIR/db.json)

set -euo pipefail

# =============================================================================
# Logging Setup
# =============================================================================

if [ -z "${MOCK_GH_LOG_DIR:-}" ]; then
    echo "Error: MOCK_GH_LOG_DIR is not set" >&2
    exit 1
fi

mkdir -p "$MOCK_GH_LOG_DIR"
mkdir -p "$MOCK_GH_LOG_DIR/args"

INVOCATION_ID=1
if [ -f "$MOCK_GH_LOG_DIR/mock-gh-invocations" ]; then
    INVOCATION_ID=$(($(cat "$MOCK_GH_LOG_DIR/mock-gh-invocations") + 1))
fi
echo "$INVOCATION_ID" > "$MOCK_GH_LOG_DIR/mock-gh-invocations"

LOG_FILE="$MOCK_GH_LOG_DIR/mock-gh-invocation-$INVOCATION_ID.log"
ARGS_FILE="$MOCK_GH_LOG_DIR/args/invocation-$INVOCATION_ID.args"

echo "$@" > "$ARGS_FILE"
printf "args: %s\n" "$*" >> "$LOG_FILE"
printf "cwd: %s\n" "$(pwd)" >> "$LOG_FILE"

debug_log() {
    if [ "${MOCK_GH_VERBOSE:-}" = "true" ]; then
        echo "[mock-gh] $*" >&2
    fi
}

debug_log "Invoked with: $*"

# =============================================================================
# Database Setup
# =============================================================================

DB_FILE="${MOCK_GH_DB:-$MOCK_GH_LOG_DIR/db.json}"

init_db() {
    if [ ! -f "$DB_FILE" ]; then
        echo '{"issues":[], "prs":[]}' > "$DB_FILE"
    fi
}

init_db

# =============================================================================
# Command Parsing & Logic
# =============================================================================

CMD="${1:-}"
SUBCMD="${2:-}"

# Handling specific forced output/exit
if [ -n "${MOCK_GH_OUTPUT:-}" ]; then
    echo -e "$MOCK_GH_OUTPUT"
    if [ -n "${MOCK_GH_EXIT_CODE:-}" ]; then
        exit "$MOCK_GH_EXIT_CODE"
    fi
    exit 0
fi

if [ -n "${MOCK_GH_EXIT_CODE:-}" ]; then
    exit "$MOCK_GH_EXIT_CODE"
fi

# Helper to read args
get_arg_value() {
    local flag="$1"
    shift
    local val=""
    while [[ $# -gt 0 ]]; do
        if [[ "$1" == "$flag" ]]; then
            val="$2"
            break
        fi
        shift
    done
    echo "$val"
}

# -----------------------------------------------------------------------------
# gh pr
# -----------------------------------------------------------------------------
if [[ "$CMD" == "pr" ]]; then
    
    if [[ "$SUBCMD" == "create" ]]; then
        # Parse args
        TITLE=$(get_arg_value "--title" "$@")
        BODY=$(get_arg_value "--body" "$@")
        
        # Determine ID
        NEXT_ID=$(jq '.prs | length + 1' "$DB_FILE")
        
        # Create PR object
        # Need to construct a JSON object. Using jq to add to the array.
        TMP_DB=$(mktemp)
        jq --arg title "$TITLE" --arg body "$BODY" --argjson id "$NEXT_ID" \
           '.prs += [{"number": $id, "title": $title, "body": $body, "state": "OPEN", "url": ("https://github.com/mock/repo/pull/" + ($id|tostring))}]' \
           "$DB_FILE" > "$TMP_DB" && mv "$TMP_DB" "$DB_FILE"
           
        echo "https://github.com/mock/repo/pull/$NEXT_ID"
        exit 0
        
    elif [[ "$SUBCMD" == "list" ]]; then
        JSON_FIELDS=$(get_arg_value "--json" "$@")
        
        if [ -n "$JSON_FIELDS" ]; then
             jq '.prs' "$DB_FILE"
        else
             # Table output
             # number, title, state
             jq -r '.prs[] | "\(.number)\t\(.title)\t\(.state)"' "$DB_FILE"
        fi
        exit 0
        
    elif [[ "$SUBCMD" == "view" ]]; then
        # gh pr view 123 --json ...
        # First arg after 'view' might be number, or it relies on current branch.
        # Simple mock: if number provided, look it up.
        # Assuming args: gh pr view <number> --json ...
        PR_NUM="$3"
        # Validate if number
        if [[ ! "$PR_NUM" =~ ^[0-9]+$ ]]; then
            # Maybe it's empty or flag, implies current PR. 
            # For mock, just return first PR or error.
            if [[ "$PR_NUM" == "--json" ]]; then
                 # No number provided, assume "current branch PR"
                 # Mock behavior: return the last created PR
                 PR_NUM=$(jq '.prs[-1].number' "$DB_FILE")
            fi
        fi
        
        JSON_FIELDS=$(get_arg_value "--json" "$@")
        if [ -n "$JSON_FIELDS" ]; then
            jq --argjson num "$PR_NUM" '.prs[] | select(.number == $num)' "$DB_FILE"
        else
            jq -r --argjson num "$PR_NUM" '.prs[] | select(.number == $num) | "\(.title)\n\(.body)"' "$DB_FILE"
        fi
        exit 0
        
    elif [[ "$SUBCMD" == "merge" ]]; then
        # gh pr merge <number>
        PR_NUM="$3"
        if [[ ! "$PR_NUM" =~ ^[0-9]+$ ]]; then
             # Assume current context = last PR
             PR_NUM=$(jq '.prs[-1].number' "$DB_FILE")
        fi
        
        # Update state to MERGED
        TMP_DB=$(mktemp)
        jq --argjson num "$PR_NUM" \
           '.prs |= map(if .number == $num then .state = "MERGED" else . end)' \
           "$DB_FILE" > "$TMP_DB" && mv "$TMP_DB" "$DB_FILE"
           
        echo "Merged pull request #$PR_NUM"
        exit 0
    fi

# -----------------------------------------------------------------------------
# gh issue
# -----------------------------------------------------------------------------
elif [[ "$CMD" == "issue" ]]; then

    if [[ "$SUBCMD" == "create" ]]; then
        TITLE=$(get_arg_value "--title" "$@")
        BODY=$(get_arg_value "--body" "$@")
        NEXT_ID=$(jq '.issues | length + 1' "$DB_FILE")
        
        TMP_DB=$(mktemp)
        jq --arg title "$TITLE" --arg body "$BODY" --argjson id "$NEXT_ID" \
           '.issues += [{"number": $id, "title": $title, "body": $body, "state": "OPEN", "url": ("https://github.com/mock/repo/issues/" + ($id|tostring))}]' \
           "$DB_FILE" > "$TMP_DB" && mv "$TMP_DB" "$DB_FILE"
           
        echo "https://github.com/mock/repo/issues/$NEXT_ID"
        exit 0
        
    elif [[ "$SUBCMD" == "list" ]]; then
        JSON_FIELDS=$(get_arg_value "--json" "$@")
        if [ -n "$JSON_FIELDS" ]; then
             jq '.issues' "$DB_FILE"
        else
             jq -r '.issues[] | "\(.number)\t\(.title)\t\(.state)"' "$DB_FILE"
        fi
        exit 0
    fi
    
# -----------------------------------------------------------------------------
# gh repo
# -----------------------------------------------------------------------------
elif [[ "$CMD" == "repo" ]]; then
    if [[ "$SUBCMD" == "view" ]]; then
        JSON_FIELDS=$(get_arg_value "--json" "$@")
        if [ -n "$JSON_FIELDS" ]; then
             echo '{"owner":{"login":"mock"}, "name":"repo"}'
        else
             echo "mock/repo"
        fi
        exit 0
    fi

fi

# Fallback for unknown commands
debug_log "Unknown command: $CMD $SUBCMD"
# If we want to simulate success for everything else:
exit 0
