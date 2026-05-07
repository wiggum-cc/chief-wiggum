#!/usr/bin/env bash
# python-lint-runner.sh - Run ruff lint on all Python projects
#
# Usage:
#   ./tests/python-lint-runner.sh          # Check lint
#   ./tests/python-lint-runner.sh --fix    # Auto-fix lint issues

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Check if uv is available
if ! command -v uv &>/dev/null; then
    echo -e "${RED}Error: uv is not installed${NC}"
    echo "Install uv: curl -LsSf https://astral.sh/uv/install.sh | sh"
    exit 1
fi

RUFF_ARGS=("check")
if [[ "${1:-}" == "--fix" ]]; then
    RUFF_ARGS+=("--fix")
    shift
fi

echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${BLUE}  Chief Wiggum Python Lint Runner${NC}"
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

ERRORS=0

# Lint TUI
echo -e "${YELLOW}Linting tui/...${NC}"
cd "$PROJECT_ROOT/tui"
uv sync --extra dev --quiet
if uv run ruff "${RUFF_ARGS[@]}" .; then
    echo -e "${GREEN}  tui/ passed ✓${NC}"
else
    echo -e "${RED}  tui/ failed ✗${NC}"
    ((++ERRORS))
fi

# Lint orchestrator-py
echo -e "${YELLOW}Linting lib/orchestrator-py/...${NC}"
cd "$PROJECT_ROOT/lib/orchestrator-py"
uv sync --extra dev --quiet
if uv run ruff "${RUFF_ARGS[@]}" .; then
    echo -e "${GREEN}  lib/orchestrator-py/ passed ✓${NC}"
else
    echo -e "${RED}  lib/orchestrator-py/ failed ✗${NC}"
    ((++ERRORS))
fi

echo ""
if [ "$ERRORS" -eq 0 ]; then
    echo -e "${GREEN}Python lint passed! ✓${NC}"
    exit 0
else
    echo -e "${RED}Python lint failed ($ERRORS projects) ✗${NC}"
    exit 1
fi
