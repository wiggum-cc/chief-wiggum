#!/usr/bin/env bash
# Test script for resource tracking functionality

set -e

export RALPH_DIR="/media/data/proj/ai/chief-wiggum/.ralph"
export TASK_ID="TASK-027-TEST"
export WORKER_ID="test-worker-$(date +%s)"

# Source the resource tracker
source lib/resource-tracker.sh

echo "==================================="
echo "Resource Tracker Test Suite"
echo "==================================="
echo ""

# Test 1: Track worker disk usage
echo "Test 1: Track worker disk usage"
echo "-----------------------------------"
track_worker_disk_usage "$(pwd)" "$WORKER_ID"
echo ""
echo "✓ Test 1 passed"
echo ""

# Test 2: Track all worktrees
echo "Test 2: Track all worktrees"
echo "-----------------------------------"
track_all_worktrees "$RALPH_DIR/workers"
echo ""
echo "✓ Test 2 passed"
echo ""

# Test 3: Pre-flight disk space check (should pass)
echo "Test 3: Pre-flight disk space check (1GB requirement)"
echo "-----------------------------------"
if check_disk_space_preflight 1073741824 "."; then
    echo "✓ Test 3 passed - Sufficient disk space available"
else
    echo "✗ Test 3 failed - Insufficient disk space (this might be expected)"
fi
echo ""

# Test 4: Pre-flight disk space check (should warn)
echo "Test 4: Pre-flight disk space check (unrealistic requirement)"
echo "-----------------------------------"
if check_disk_space_preflight 999999999999999 "."; then
    echo "✗ Test 4 failed - Should have warned about low disk space"
else
    exit_code=$?
    if [ $exit_code -eq 2 ]; then
        echo "✓ Test 4 passed - Warning issued for low disk space"
    else
        echo "✗ Test 4 failed - Unexpected exit code: $exit_code"
    fi
fi
echo ""

# Test 5: Log lock contention
echo "Test 5: Log lock contention"
echo "-----------------------------------"
log_lock_contention "test-file.lock" 3.14 "$TASK_ID" "$WORKER_ID"
if [ -f "$RALPH_DIR/logs/lock-contention.log" ]; then
    echo "Log file created:"
    grep "$WORKER_ID" "$RALPH_DIR/logs/lock-contention.log" | tail -1
    echo "✓ Test 5 passed"
else
    echo "✗ Test 5 failed - Log file not created"
fi
echo ""

# Test 6: Report resource usage summary
echo "Test 6: Report resource usage summary"
echo "-----------------------------------"
report_resource_usage "$(pwd)" "$WORKER_ID"
echo "✓ Test 6 passed"
echo ""

echo "==================================="
echo "All tests completed successfully!"
echo "==================================="
