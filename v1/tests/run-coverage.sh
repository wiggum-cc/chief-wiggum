#!/usr/bin/env bash
# run-coverage.sh - Run tests with code coverage using kcov
#
# Usage:
#   ./tests/run-coverage.sh              # Run with kcov (if installed)
#   ./tests/run-coverage.sh --install    # Install kcov on Debian/Ubuntu
#   ./tests/run-coverage.sh --report     # Show coverage summary
#   ./tests/run-coverage.sh --html       # Open HTML report
#
# Requirements:
#   kcov (https://github.com/SimonKagworthy/kcov)
#
# Output:
#   Coverage reports are written to tests/coverage/
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
COVERAGE_DIR="$SCRIPT_DIR/coverage"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Check for kcov
check_kcov() {
    if ! command -v kcov &>/dev/null; then
        echo -e "${RED}kcov not installed.${NC}"
        echo ""
        echo "Install options:"
        echo "  Debian/Ubuntu: sudo apt-get install kcov"
        echo "  Arch Linux:    sudo pacman -S kcov"
        echo "  From source:   https://github.com/SimonKagstrom/kcov"
        echo ""
        echo "Or run: $0 --install"
        return 1
    fi
    echo -e "${GREEN}kcov found:${NC} $(kcov --version 2>&1 | head -1)"
    return 0
}

# Install kcov (Debian/Ubuntu)
install_kcov() {
    echo "Installing kcov..."
    if command -v apt-get &>/dev/null; then
        sudo apt-get update && sudo apt-get install -y kcov
    elif command -v pacman &>/dev/null; then
        sudo pacman -S --noconfirm kcov
    else
        echo "Cannot determine package manager. Please install kcov manually."
        echo "See: https://github.com/SimonKagstrom/kcov"
        exit 1
    fi
}

# Run a single test file with coverage
run_with_coverage() {
    local test_file="$1"
    local test_name
    test_name=$(basename "$test_file" .sh)
    local test_coverage_dir="$COVERAGE_DIR/$test_name"

    echo -e "${BLUE}Coverage:${NC} $test_name"

    # kcov options:
    #   --include-path: Only track coverage for our lib/ and bin/ files
    #   --exclude-pattern: Skip test files themselves
    kcov \
        --include-path="$PROJECT_ROOT/lib,$PROJECT_ROOT/bin" \
        --exclude-pattern="tests/,/tmp/,.git/" \
        "$test_coverage_dir" \
        bash "$test_file" >/dev/null 2>&1 || true
}

# Merge all individual coverage reports
merge_coverage() {
    echo ""
    echo -e "${BLUE}Merging coverage reports...${NC}"

    local merge_dirs=()
    for dir in "$COVERAGE_DIR"/test_*; do
        [ -d "$dir" ] && merge_dirs+=("$dir")
    done

    if [ ${#merge_dirs[@]} -eq 0 ]; then
        echo -e "${YELLOW}No coverage data found${NC}"
        return 1
    fi

    kcov --merge "$COVERAGE_DIR/merged" "${merge_dirs[@]}" >/dev/null 2>&1 || true
}

# Show coverage summary
show_summary() {
    local merged_dir="$COVERAGE_DIR/merged"

    if [ ! -d "$merged_dir" ]; then
        echo -e "${RED}No merged coverage data. Run tests first.${NC}"
        return 1
    fi

    echo ""
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${BLUE}  Code Coverage Summary${NC}"
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"

    # Parse the coverage JSON if available
    local coverage_json="$merged_dir/coverage.json"
    if [ -f "$coverage_json" ]; then
        local total_lines covered_lines percent
        total_lines=$(jq '.total_lines // 0' "$coverage_json" 2>/dev/null || echo "0")
        covered_lines=$(jq '.covered_lines // 0' "$coverage_json" 2>/dev/null || echo "0")
        percent=$(jq -r '.percent_covered // "0"' "$coverage_json" 2>/dev/null || echo "0")

        echo ""
        echo -e "  Total lines:   $total_lines"
        echo -e "  Covered lines: $covered_lines"
        echo -e "  Coverage:      ${GREEN}${percent}%${NC}"
        echo ""

        # Per-file breakdown from kcov output
        if [ -f "$merged_dir/index.json" ]; then
            echo "  Per-file coverage:"
            jq -r '.files[] | "    \(.file): \(.percent_covered)%"' "$merged_dir/index.json" 2>/dev/null | \
                sort -t: -k2 -n | head -30
        fi
    else
        echo ""
        echo "  Coverage JSON not found. Check $merged_dir/index.html for HTML report."
    fi

    echo ""
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""
    echo -e "HTML report: ${BLUE}file://$merged_dir/index.html${NC}"
}

# Main execution
main() {
    case "${1:-}" in
        --install)
            install_kcov
            exit 0
            ;;
        --report)
            show_summary
            exit 0
            ;;
        --html)
            local html="$COVERAGE_DIR/merged/index.html"
            if [ -f "$html" ]; then
                xdg-open "$html" 2>/dev/null || open "$html" 2>/dev/null || echo "Open: $html"
            else
                echo "No HTML report found. Run tests first."
            fi
            exit 0
            ;;
    esac

    # Check kcov is available
    if ! check_kcov; then
        exit 1
    fi

    # Clean previous coverage
    [ -n "$COVERAGE_DIR" ] && rm -rf "$COVERAGE_DIR"
    mkdir -p "$COVERAGE_DIR"

    echo ""
    echo -e "${BLUE}Running tests with coverage...${NC}"
    echo ""

    # Find all test files
    local test_count=0
    while IFS= read -r -d '' test_file; do
        run_with_coverage "$test_file"
        ((test_count++))
    done < <(find "$SCRIPT_DIR" -maxdepth 1 -name "test_*.sh" -type f -print0 | sort -z)

    echo ""
    echo -e "Ran $test_count test files with coverage"

    # Merge reports
    merge_coverage

    # Show summary
    show_summary
}

main "$@"
