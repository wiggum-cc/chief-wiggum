#!/usr/bin/env bash
set -euo pipefail
# Tests for install.sh rsync behavior
#
# Verifies that:
# - Expected directories are copied correctly
# - Generated artifacts (.venv, __pycache__, etc.) are excluded
# - Symlinks inside .venv do not cause failures

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

source "$TESTS_DIR/test-framework.sh"

SRC_DIR=""
TARGET_DIR=""

setup() {
    SRC_DIR=$(mktemp -d)
    TARGET_DIR=$(mktemp -d)

    mkdir -p "$SRC_DIR/bin"
    echo '#!/bin/bash' > "$SRC_DIR/bin/wiggum"
    chmod +x "$SRC_DIR/bin/wiggum"

    mkdir -p "$SRC_DIR/lib/core"
    echo 'echo core' > "$SRC_DIR/lib/core/logger.sh"

    mkdir -p "$SRC_DIR/lib/orchestrator-py"
    echo '[project]' > "$SRC_DIR/lib/orchestrator-py/pyproject.toml"
    echo 'main.py' > "$SRC_DIR/lib/orchestrator-py/main.py"

    mkdir -p "$SRC_DIR/config"
    echo '{}' > "$SRC_DIR/config/config.json"

    mkdir -p "$SRC_DIR/tui"
    echo '[project]' > "$SRC_DIR/tui/pyproject.toml"
    echo 'app.py' > "$SRC_DIR/tui/app.py"

    mkdir -p "$SRC_DIR/hooks/callbacks"
    echo '#!/bin/bash' > "$SRC_DIR/hooks/callbacks/on-done.sh"

    mkdir -p "$SRC_DIR/skills"
    echo 'skill' > "$SRC_DIR/skills/README.md"

    # Artifacts that should be excluded
    mkdir -p "$SRC_DIR/tui/.venv/bin"
    ln -s /usr/bin/python3 "$SRC_DIR/tui/.venv/bin/python3"
    echo 'fake' > "$SRC_DIR/tui/.venv/pyvenv.cfg"

    mkdir -p "$SRC_DIR/lib/orchestrator-py/.venv/bin"
    ln -s /usr/bin/python3 "$SRC_DIR/lib/orchestrator-py/.venv/bin/python3"

    mkdir -p "$SRC_DIR/tui/__pycache__"
    echo 'bytecode' > "$SRC_DIR/tui/__pycache__/app.cpython-312.pyc"

    mkdir -p "$SRC_DIR/lib/orchestrator-py/__pycache__"
    echo 'bytecode' > "$SRC_DIR/lib/orchestrator-py/__pycache__/main.cpython-312.pyc"

    mkdir -p "$SRC_DIR/tui/tui.egg-info"
    echo 'metadata' > "$SRC_DIR/tui/tui.egg-info/PKG-INFO"

    mkdir -p "$SRC_DIR/tui/.pytest_cache/v/cache"
    echo '{}' > "$SRC_DIR/tui/.pytest_cache/v/cache/lastfailed"
}

teardown() {
    [[ -n "$SRC_DIR" ]] && rm -rf "$SRC_DIR"
    [[ -n "$TARGET_DIR" ]] && rm -rf "$TARGET_DIR"
}

_run_install_rsync() {
    rsync -a \
        --exclude '.venv' \
        --exclude '__pycache__' \
        --exclude '*.egg-info' \
        --exclude '.pytest_cache' \
        "$SRC_DIR/bin" \
        "$SRC_DIR/lib" \
        "$SRC_DIR/hooks" \
        "$SRC_DIR/skills" \
        "$SRC_DIR/config" \
        "$SRC_DIR/tui" \
        "$TARGET_DIR/"
}

_assert_dir_not_exists() {
    local dir_path="$1"
    local message="${2:-Directory should not exist: $dir_path}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if [[ ! -d "$dir_path" ]]; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}Directory exists: $dir_path${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# =============================================================================
# Tests
# =============================================================================

test_rsync_copies_expected_directories() {
    _run_install_rsync

    assert_dir_exists "$TARGET_DIR/bin" "bin/ should be copied"
    assert_dir_exists "$TARGET_DIR/lib" "lib/ should be copied"
    assert_dir_exists "$TARGET_DIR/lib/core" "lib/core/ should be copied"
    assert_dir_exists "$TARGET_DIR/lib/orchestrator-py" "lib/orchestrator-py/ should be copied"
    assert_dir_exists "$TARGET_DIR/hooks" "hooks/ should be copied"
    assert_dir_exists "$TARGET_DIR/hooks/callbacks" "hooks/callbacks/ should be copied"
    assert_dir_exists "$TARGET_DIR/skills" "skills/ should be copied"
    assert_dir_exists "$TARGET_DIR/config" "config/ should be copied"
    assert_dir_exists "$TARGET_DIR/tui" "tui/ should be copied"
}

test_rsync_copies_file_contents() {
    _run_install_rsync

    assert_file_exists "$TARGET_DIR/bin/wiggum" "bin/wiggum should be copied"
    assert_file_exists "$TARGET_DIR/lib/core/logger.sh" "lib/core/logger.sh should be copied"
    assert_file_exists "$TARGET_DIR/lib/orchestrator-py/pyproject.toml" "orchestrator-py/pyproject.toml should be copied"
    assert_file_exists "$TARGET_DIR/lib/orchestrator-py/main.py" "orchestrator-py/main.py should be copied"
    assert_file_exists "$TARGET_DIR/config/config.json" "config/config.json should be copied"
    assert_file_exists "$TARGET_DIR/tui/pyproject.toml" "tui/pyproject.toml should be copied"
    assert_file_exists "$TARGET_DIR/tui/app.py" "tui/app.py should be copied"
    assert_file_exists "$TARGET_DIR/hooks/callbacks/on-done.sh" "hooks callback should be copied"
    assert_file_exists "$TARGET_DIR/skills/README.md" "skills/README.md should be copied"
}

test_rsync_excludes_venv() {
    _run_install_rsync

    _assert_dir_not_exists "$TARGET_DIR/tui/.venv" "tui/.venv should NOT be copied"
    _assert_dir_not_exists "$TARGET_DIR/lib/orchestrator-py/.venv" "orchestrator-py/.venv should NOT be copied"
}

test_rsync_excludes_pycache() {
    _run_install_rsync

    _assert_dir_not_exists "$TARGET_DIR/tui/__pycache__" "tui/__pycache__ should NOT be copied"
    _assert_dir_not_exists "$TARGET_DIR/lib/orchestrator-py/__pycache__" "orchestrator-py/__pycache__ should NOT be copied"
}

test_rsync_excludes_egg_info() {
    _run_install_rsync

    _assert_dir_not_exists "$TARGET_DIR/tui/tui.egg-info" "tui.egg-info should NOT be copied"
}

test_rsync_excludes_pytest_cache() {
    _run_install_rsync

    _assert_dir_not_exists "$TARGET_DIR/tui/.pytest_cache" ".pytest_cache should NOT be copied"
}

test_rsync_idempotent() {
    _run_install_rsync
    _run_install_rsync

    assert_file_exists "$TARGET_DIR/bin/wiggum" "bin/wiggum should still exist after second rsync"
    _assert_dir_not_exists "$TARGET_DIR/tui/.venv" ".venv should still be excluded after second rsync"
}

test_rsync_exit_code() {
    local exit_code=0
    _run_install_rsync || exit_code=$?

    assert_equals "0" "$exit_code" "rsync should exit 0"
}

# =============================================================================
# Run
# =============================================================================

run_test test_rsync_copies_expected_directories
run_test test_rsync_copies_file_contents
run_test test_rsync_excludes_venv
run_test test_rsync_excludes_pycache
run_test test_rsync_excludes_egg_info
run_test test_rsync_excludes_pytest_cache
run_test test_rsync_idempotent
run_test test_rsync_exit_code

print_test_summary
exit_with_test_result
