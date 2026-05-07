#!/usr/bin/env bash
# tui-test-runner.sh - Run Python TUI test suite
#
# Usage:
#   ./tests/tui-test-runner.sh              # Run all TUI tests
#   ./tests/tui-test-runner.sh -k kanban    # Run tests matching pattern
#   ./tests/tui-test-runner.sh -v           # Verbose output
#   ./tests/tui-test-runner.sh --coverage   # Run with coverage

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TUI_DIR="$PROJECT_ROOT/tui"

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

# Check TUI directory exists
if [ ! -d "$TUI_DIR" ]; then
    echo -e "${RED}Error: TUI directory not found at $TUI_DIR${NC}"
    exit 1
fi

cd "$TUI_DIR"

echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${BLUE}  Chief Wiggum TUI Test Runner${NC}"
echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo ""

# Ensure dev dependencies are installed
echo -e "${YELLOW}Syncing dependencies...${NC}"
uv sync --extra dev --quiet

echo -e "${YELLOW}Running pytest...${NC}"
echo ""

# Run pytest with all arguments passed through
if uv run pytest tests/ "$@"; then
    echo ""
    echo -e "${GREEN}TUI tests passed! ✓${NC}"
    exit 0
else
    echo ""
    echo -e "${RED}TUI tests failed ✗${NC}"
    exit 1
fi
