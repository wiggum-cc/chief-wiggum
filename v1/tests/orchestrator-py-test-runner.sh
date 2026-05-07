#!/usr/bin/env bash
# orchestrator-py-test-runner.sh - Run orchestrator-py Python test suite
#
# Usage:
#   ./tests/orchestrator-py-test-runner.sh              # Run all tests
#   ./tests/orchestrator-py-test-runner.sh -k scheduler # Run tests matching pattern
#   ./tests/orchestrator-py-test-runner.sh -v           # Verbose output

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
ORCH_DIR="$PROJECT_ROOT/lib/orchestrator-py"

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

# Check directory exists
if [ ! -d "$ORCH_DIR" ]; then
    echo -e "${RED}Error: orchestrator-py directory not found at $ORCH_DIR${NC}"
    exit 1
fi

cd "$ORCH_DIR"

echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${BLUE}  Chief Wiggum Orchestrator-py Test Runner${NC}"
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
    echo -e "${GREEN}Orchestrator-py tests passed! ✓${NC}"
    exit 0
else
    echo ""
    echo -e "${RED}Orchestrator-py tests failed ✗${NC}"
    exit 1
fi
