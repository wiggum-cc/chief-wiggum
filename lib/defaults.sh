#!/usr/bin/env bash
# defaults.sh - Centralized configuration defaults and path setup
#
# Source this file early in any wiggum script to get consistent defaults.
# All values can be overridden by environment variables.

# Core paths
WIGGUM_HOME="${WIGGUM_HOME:-$HOME/.claude/chief-wiggum}"
PROJECT_DIR="${PROJECT_DIR:-$(pwd)}"
RALPH_DIR="${RALPH_DIR:-$PROJECT_DIR/.ralph}"

# Worker configuration defaults
MAX_WORKERS="${WIGGUM_MAX_WORKERS:-4}"
MAX_ITERATIONS="${WIGGUM_MAX_ITERATIONS:-20}"
MAX_TURNS="${WIGGUM_MAX_TURNS:-50}"

# Export for child processes
export WIGGUM_HOME
export PROJECT_DIR
export RALPH_DIR
export WIGGUM_MAX_ITERATIONS="$MAX_ITERATIONS"
export WIGGUM_MAX_TURNS="$MAX_TURNS"
