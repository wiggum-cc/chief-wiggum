#!/usr/bin/env bash
# verify-git-stash.sh - PostToolUse hook to verify git stash state after Bash commands
#
# Ensures no stash entries were leaked by a Bash command that used git stash.
# Reads the pre-execution stash count from .stash-guard (written by PreToolUse)
# and compares to current state. If stash entries leaked (e.g., command failed
# between stash and pop), automatically pops them and logs a warning.
#
# Exit codes: 0 = always (PostToolUse hooks are informational, not blocking)

set -euo pipefail

# Read JSON input from stdin
input=$(cat)

tool=$(echo "$input" | jq -r '.tool // empty')

# Only applies to Bash commands
[[ "$tool" != "Bash" ]] && exit 0

workspace="${WORKER_WORKSPACE:-${CLAUDE_PROJECT_DIR:-}}"
worker_dir="${WORKER_DIR:-}"

# Must have both workspace and worker_dir
[[ -z "$worker_dir" || -z "$workspace" ]] && exit 0

guard_file="$worker_dir/.stash-guard"

# No guard file means PreToolUse didn't flag a stash command
[[ ! -f "$guard_file" ]] && exit 0

# Read expected stash count and clean up guard file
expected_count=$(cat "$guard_file")
expected_count="${expected_count:-0}"
rm -f "$guard_file"

# Get current stash count
current_count=$(cd "$workspace" && git stash list 2>/dev/null | wc -l || echo "0")
current_count="${current_count:-0}"

# If stash count is at or below expected, all good
if [[ "$current_count" -le "$expected_count" ]]; then
    exit 0
fi

# Stash leaked - clean up
leaked=$((current_count - expected_count))
log_file="$worker_dir/hook-decisions.log"
timestamp=$(date -Iseconds 2>/dev/null || date +%Y-%m-%dT%H:%M:%S)

echo "[$timestamp] STASH-GUARD | leaked=$leaked | expected=$expected_count actual=$current_count | auto-popping" >> "$log_file" 2>/dev/null || true

# Pop leaked stash entries (most recent first)
for ((i = 0; i < leaked; i++)); do
    pop_exit=0
    cd "$workspace" && git stash pop 2>/dev/null || pop_exit=$?
    if [[ "$pop_exit" -ne 0 ]]; then
        echo "[$timestamp] STASH-GUARD | WARNING: git stash pop failed (exit=$pop_exit) on iteration $i, dropping entry" >> "$log_file" 2>/dev/null || true
        # If pop fails (e.g., conflicts), drop the entry to prevent stash buildup
        cd "$workspace" && git stash drop 2>/dev/null || true
    fi
done

# Log final state
final_count=$(cd "$workspace" && git stash list 2>/dev/null | wc -l || echo "0")
final_count="${final_count:-0}"
echo "[$timestamp] STASH-GUARD | cleanup complete | final_count=$final_count" >> "$log_file" 2>/dev/null || true

exit 0
