#!/usr/bin/env bash
# mock-gh-helpers.sh - Helpers for mock-gh.sh

mock_gh_setup() {
    if [ -z "${MOCK_DIR:-}" ]; then
        MOCK_DIR=$(mktemp -d)
    fi
    export MOCK_GH_LOG_DIR="$MOCK_DIR/gh-logs"
    mkdir -p "$MOCK_GH_LOG_DIR"
    
    MOCK_GH_PATH="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/mock-gh.sh"
    chmod +x "$MOCK_GH_PATH"
    
    mkdir -p "$MOCK_DIR/bin"
    ln -sf "$MOCK_GH_PATH" "$MOCK_DIR/bin/gh"
    export PATH="$MOCK_DIR/bin:$PATH"
    
    unset MOCK_GH_EXIT_CODE
    unset MOCK_GH_OUTPUT
    unset MOCK_GH_SCENARIO
    unset MOCK_GH_DB
}

mock_gh_teardown() {
    unset MOCK_GH_LOG_DIR
    unset MOCK_GH_EXIT_CODE
    unset MOCK_GH_OUTPUT
    unset MOCK_GH_SCENARIO
    unset MOCK_GH_DB
}

assert_gh_invoked_with() {
    local index="$1"
    local expected_arg="$2"
    local message="${3:-Gh invocation $index should contain '$expected_arg'}"
    
    local args_file="$MOCK_GH_LOG_DIR/args/invocation-$index.args"
    if [ ! -f "$args_file" ]; then
         echo -e "  ${RED}✗${NC} $message (Invocation $index not found)"
         FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
         return 1
    fi
    
    if grep -qF -- "$expected_arg" "$args_file"; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message"
        echo "    Expected: $expected_arg"
        echo "    Actual: $(cat "$args_file")"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}
