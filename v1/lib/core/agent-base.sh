#!/usr/bin/env bash
# =============================================================================
# agent-base.sh - Base library for agent development
#
# Provides shared functions to reduce boilerplate across agents:
#   - Metadata setup (agent_init_metadata)
#   - Callback context management (agent_setup_context)
#   - Common dependency sourcing (agent_source_*)
#   - Default lifecycle hook implementations
#
# This file is a facade that sources the split modules for maintainability:
#   - agent-metadata.sh - Metadata, context, sourcing, lifecycle hooks
#   - agent-config.sh   - Configuration loading, result mappings
#   - agent-stream.sh   - Stream-JSON parsing utilities
#   - agent-result.sh   - Result handling, communication protocol
#
# Usage:
#   source "$WIGGUM_HOME/lib/core/agent-base.sh"
#   agent_init_metadata "my-agent" "Description of what it does"
#   agent_source_core
#   agent_source_ralph
# =============================================================================
set -euo pipefail

# Double-source prevention
# Note: We can't use a simple guard because subshells inherit the variable
# but NOT the function definitions. Instead, we check if our functions exist.
if ! type agent_init_metadata &>/dev/null; then
    # Functions not defined - need to source (first time or in subshell)
    _AGENT_BASE_LOADED=1
else
    # Functions already defined - skip re-sourcing
    return 0
fi

# Source the split modules
# Order matters: metadata provides platform.sh and context variables used by others
#                config provides result mappings used by result
#                stream provides extraction used by result
source "$WIGGUM_HOME/lib/core/agent-metadata.sh"
source "$WIGGUM_HOME/lib/core/agent-config.sh"
source "$WIGGUM_HOME/lib/core/agent-stream.sh"
source "$WIGGUM_HOME/lib/core/agent-result.sh"
