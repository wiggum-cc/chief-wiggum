#!/usr/bin/env bash
# Benchmark wiggum startup (source loading phase only)
#
# Usage:
#   ./benchmark-startup.sh [iterations]
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(cd "$SCRIPT_DIR/.." && pwd)"
ITERATIONS="${1:-10}"

cd "$WIGGUM_HOME"

# The exact sources from bin/wiggum-run
SOURCES=(
    "lib/core/exit-codes.sh"
    "lib/core/defaults.sh"
    "lib/core/verbose-flags.sh"
    "lib/core/logger.sh"
    "lib/core/file-lock.sh"
    "lib/utils/audit-logger.sh"
    "lib/utils/activity-log.sh"
    "lib/worker/worker-lifecycle.sh"
    "lib/worker/git-state.sh"
    "lib/runtime/runtime.sh"
    "lib/backend/claude/usage-tracker.sh"
    "lib/git/worktree-helpers.sh"
    "lib/tasks/task-parser.sh"
    "lib/tasks/plan-parser.sh"
    "lib/tasks/conflict-detection.sh"
    "lib/scheduler/scheduler.sh"
    "lib/scheduler/conflict-queue.sh"
    "lib/scheduler/conflict-registry.sh"
    "lib/scheduler/pr-merge-optimizer.sh"
    "lib/scheduler/orchestrator-functions.sh"
    "lib/scheduler/smart-routing.sh"
    "lib/distributed/scheduler-integration.sh"
    "lib/service/service-scheduler.sh"
    "lib/service-handlers/orchestrator-handlers.sh"
    "lib/orchestrator/migration.sh"
    "lib/orchestrator/lifecycle.sh"
    "lib/orchestrator/arg-parser.sh"
)

# Build source command
SRC_CMD=""
for src in "${SOURCES[@]}"; do
    SRC_CMD+="source \$WIGGUM_HOME/$src;"
done

echo "=== Wiggum Startup Benchmark ==="
echo "WIGGUM_HOME: $WIGGUM_HOME"
echo "Iterations: $ITERATIONS"
echo "Sources: ${#SOURCES[@]} files"
echo ""

# Warmup
bash -c "WIGGUM_HOME=$WIGGUM_HOME $SRC_CMD" >/dev/null 2>&1 || true

# Run iterations
declare -a TIMES=()
for i in $(seq 1 "$ITERATIONS"); do
    start=$(date +%s.%N)
    bash -c "WIGGUM_HOME=$WIGGUM_HOME $SRC_CMD" >/dev/null 2>&1 || true
    end=$(date +%s.%N)
    elapsed=$(echo "$end - $start" | bc)
    TIMES+=("$elapsed")
    printf "Run %2d: %.4fs\n" "$i" "$elapsed"
done

# Calculate stats
sum=0
min=${TIMES[0]}
max=${TIMES[0]}
for t in "${TIMES[@]}"; do
    sum=$(echo "$sum + $t" | bc)
    if (( $(echo "$t < $min" | bc -l) )); then min=$t; fi
    if (( $(echo "$t > $max" | bc -l) )); then max=$t; fi
done
avg=$(echo "scale=4; $sum / $ITERATIONS" | bc)

echo ""
echo "=== Results ==="
printf "Min:  %.4fs\n" "$min"
printf "Max:  %.4fs\n" "$max"
printf "Avg:  %.4fs\n" "$avg"
printf "Sum:  %.4fs\n" "$sum"
