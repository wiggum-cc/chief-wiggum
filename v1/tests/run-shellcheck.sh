#!/usr/bin/env bash
# Replicates CI shellcheck lint locally
set -euo pipefail

cd "$(dirname "$0")/.."

echo "=== Shellcheck Lint ==="
echo ""

# Exclude SC1091 (not following sourced files) since we don't use -x
SC_OPTS=(--severity=warning -e SC1091)

errors=0
checked=0

check_files() {
    local label="$1"
    shift
    local count=0

    echo -n "Checking $label... "

    for f in "$@"; do
        [ -f "$f" ] || continue
        ((++checked))
        ((++count))
        if ! shellcheck "${SC_OPTS[@]}" "$f" >/dev/null 2>&1; then
            echo "✗ $f"
            # Re-run to show the error
            shellcheck "${SC_OPTS[@]}" "$f" 2>&1 | head -5
            ((++errors))
        else
            echo "✓"
        fi
    done

    echo "$count files"
}

# Use explicit finds to avoid glob/quoting issues
mapfile -t bin_files < <(find bin -type f -executable 2>/dev/null)
mapfile -t lib_files < <(find lib -name "*.sh" -type f 2>/dev/null)
mapfile -t test_files < <(find tests -name "*.sh" -type f 2>/dev/null)
mapfile -t hook_files < <(find hooks -name "*.sh" -type f 2>/dev/null)

check_files "bin scripts" "${bin_files[@]}"
check_files "lib scripts" "${lib_files[@]}"
check_files "test scripts" "${test_files[@]}"
[ ${#hook_files[@]} -gt 0 ] && check_files "hooks scripts" "${hook_files[@]}"
check_files "root scripts" install.sh install-symlink.sh

echo ""
if [ $errors -gt 0 ]; then
    echo "Shellcheck found issues in $errors of $checked files"
    exit 1
fi

echo "All $checked files passed shellcheck!"
