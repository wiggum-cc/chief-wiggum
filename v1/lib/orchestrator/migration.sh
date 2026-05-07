#!/usr/bin/env bash
# =============================================================================
# migration.sh - Migrate old .ralph/ file paths to new directory structure
#
# Moves orchestrator state files from .ralph/ root into .ralph/orchestrator/
# and service state files into .ralph/services/. This is a one-time operation
# that runs at startup.
#
# Provides:
#   _ensure_orchestrator_dirs()  - Create required directories
#   _migrate_ralph_layout()      - Move old paths to new paths
# =============================================================================

[ -n "${_ORCHESTRATOR_MIGRATION_LOADED:-}" ] && return 0
_ORCHESTRATOR_MIGRATION_LOADED=1
source "$WIGGUM_HOME/lib/core/safe-path.sh"

# Create required orchestrator and service directories
#
# Args:
#   ralph_dir - Ralph directory path
_ensure_orchestrator_dirs() {
    local ralph_dir="${1:-$RALPH_DIR}"
    safe_path "$ralph_dir" "ralph_dir" || return 1
    mkdir -p "$ralph_dir/orchestrator"
    mkdir -p "$ralph_dir/services"
}

# Migrate old .ralph/ file layout to new directory structure
#
# For each old path, if the old file exists and the new one doesn't,
# move it. Lock files move alongside their protected resources.
#
# Args:
#   ralph_dir - Ralph directory path
_migrate_ralph_layout() {
    local ralph_dir="${1:-$RALPH_DIR}"

    _ensure_orchestrator_dirs "$ralph_dir"

    # Migration map: old_path -> new_path
    # Orchestrator state files
    _migrate_file "$ralph_dir/.orchestrator.pid"              "$ralph_dir/orchestrator/orchestrator.pid"
    _migrate_file "$ralph_dir/.pool-pending"                  "$ralph_dir/orchestrator/pool-pending"
    _migrate_file "$ralph_dir/.pool-pending.lock"             "$ralph_dir/orchestrator/pool-pending.lock"
    _migrate_file "$ralph_dir/.tasks-needing-fix.txt"         "$ralph_dir/orchestrator/tasks-needing-fix.txt"
    _migrate_file "$ralph_dir/.task-ready-since"              "$ralph_dir/orchestrator/task-ready-since"
    _migrate_file "$ralph_dir/.priority-worker-count"         "$ralph_dir/orchestrator/priority-worker-count"
    _migrate_file "$ralph_dir/.priority-worker-count.lock"    "$ralph_dir/orchestrator/priority-worker-count.lock"
    _migrate_file "$ralph_dir/.prs-needing-workspace.jsonl"   "$ralph_dir/orchestrator/prs-needing-workspace.jsonl"
    _migrate_file "$ralph_dir/.sync-state.json"               "$ralph_dir/orchestrator/sync-state.json"
    _migrate_file "$ralph_dir/.conflict-registry.json"        "$ralph_dir/orchestrator/conflict-registry.json"
    _migrate_file "$ralph_dir/.pid-ops.lock"                  "$ralph_dir/orchestrator/pid-ops.lock"
    _migrate_file "$ralph_dir/pr-merge-state.json"            "$ralph_dir/orchestrator/pr-merge-state.json"
    _migrate_file "$ralph_dir/claude-usage.json"              "$ralph_dir/orchestrator/claude-usage.json"

    # Service state files
    _migrate_file "$ralph_dir/.service-state.json"            "$ralph_dir/services/state.json"
    _migrate_file "$ralph_dir/.service-metrics.jsonl"         "$ralph_dir/services/metrics.jsonl"
    _migrate_file "$ralph_dir/.heartbeat"                     "$ralph_dir/services/heartbeat"
}

# Move a single file from old path to new path (if needed)
#
# Args:
#   old_path - Source path
#   new_path - Destination path
_migrate_file() {
    local old_path="$1"
    local new_path="$2"

    # Only migrate if old exists and new doesn't
    if [ -e "$old_path" ] && [ ! -e "$new_path" ]; then
        mv "$old_path" "$new_path"
    fi
}
