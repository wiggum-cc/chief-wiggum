#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: workflow.git-conflict-resolver
# AGENT_DESCRIPTION: Workflow variant of git conflict resolver.
#   Thin wrapper that delegates to engineering.git-conflict-resolver.
#   Both versions now support resolution-plan.md for coordinated multi-PR resolution.
# =============================================================================

# Delegate to the consolidated engineering implementation
# The engineering version now supports all workflow features including:
#   - resolution-plan.md support
#   - Pre-flight commit of uncommitted changes
#   - Broken worktree detection
source "$WIGGUM_HOME/lib/agents/engineering/git-conflict-resolver.sh"

# Override metadata for workflow variant
agent_init_metadata "workflow.git-conflict-resolver" "Git merge conflict resolver with optional coordination plan support (workflow variant)"
