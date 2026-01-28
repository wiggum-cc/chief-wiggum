#!/usr/bin/env bash
# =============================================================================
# orchestrator-handlers.sh - Service handlers for orchestrator functions
#
# This module provides the ONLY functions callable by the service scheduler.
# All service handler functions MUST:
#   1. Be defined in files under lib/services/
#   2. Use the svc_* prefix (enforced by service-runner.sh)
#
# These are thin wrappers around the orchestrator functions in
# lib/scheduler/orchestrator-functions.sh. The wrapper pattern provides:
#   - Security boundary (only svc_* functions can be invoked via services.json)
#   - Clear contract for what services can do
#   - Centralized location for all service entry points
#
# Naming convention: svc_orch_* for orchestrator-related handlers
# =============================================================================

# Prevent double-sourcing
[ -n "${_SERVICE_HANDLERS_ORCH_LOADED:-}" ] && return 0
_SERVICE_HANDLERS_ORCH_LOADED=1

# =============================================================================
# Orchestrator Service Handlers
#
# Each handler wraps a function from lib/scheduler/orchestrator-functions.sh
# =============================================================================

# Update shared usage data for rate limiting
svc_orch_usage_tracker_write_shared() {
    orch_usage_tracker_write_shared "$@"
}

# Create workspaces for orphaned PRs
svc_orch_create_orphan_pr_workspaces() {
    orch_create_orphan_pr_workspaces "$@"
}

# Spawn PR optimizer in background
svc_orch_spawn_pr_optimizer() {
    orch_spawn_pr_optimizer "$@"
}

# Check for completed PR optimizer
svc_orch_check_pr_optimizer() {
    orch_check_pr_optimizer "$@"
}

# Check for conflict batches and spawn multi-PR planner
svc_orch_spawn_multi_pr_planner() {
    orch_spawn_multi_pr_planner "$@"
}

# Spawn fix workers for PR comment issues
svc_orch_spawn_fix_workers() {
    orch_spawn_fix_workers "$@"
}

# Spawn resolve workers for merge conflicts
svc_orch_spawn_resolve_workers() {
    orch_spawn_resolve_workers "$@"
}

# Clean up finished main workers
svc_orch_cleanup_main_workers() {
    orch_cleanup_main_workers "$@"
}

# Clean up finished/timed-out fix workers
svc_orch_cleanup_fix_workers() {
    orch_cleanup_fix_workers "$@"
}

# Clean up finished/timed-out resolve workers
svc_orch_cleanup_resolve_workers() {
    orch_cleanup_resolve_workers "$@"
}

# Spawn workers for ready tasks
svc_orch_spawn_ready_tasks() {
    orch_spawn_ready_tasks "$@"
}

# Clean up all finished workers (main, fix, resolve)
svc_orch_cleanup_all_workers() {
    orch_cleanup_all_workers "$@"
}

# Display orchestrator status on scheduling events
svc_orch_display_status() {
    orch_display_status "$@"
}
