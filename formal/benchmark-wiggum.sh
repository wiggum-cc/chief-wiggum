#!/usr/bin/env bash
# Benchmark wiggum run using perf
#
# Usage:
#   ./benchmark-wiggum.sh [stat|record|flame]
#
# Modes:
#   stat   - Basic performance counters (default)
#   record - Detailed profiling for hotspot analysis
#   flame  - Generate flame graph SVG
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(cd "$SCRIPT_DIR/.." && pwd)"
RESULTS_DIR="$SCRIPT_DIR/benchmark-results"
TIMESTAMP=$(date +%Y%m%d-%H%M%S)

# Export environment
export WIGGUM_HOME
export PATH="$WIGGUM_HOME/bin:$PATH"
cd "$WIGGUM_HOME"

# Create results directory
mkdir -p "$RESULTS_DIR"

# Benchmark configuration
DURATION_SECONDS=${BENCH_DURATION:-10}
MAX_WORKERS=${BENCH_MAX_WORKERS:-1}

echo "=== Wiggum Run Benchmark ==="
echo "WIGGUM_HOME: $WIGGUM_HOME"
echo "Duration: ${DURATION_SECONDS}s"
echo "Mode: ${1:-stat}"
echo "Results: $RESULTS_DIR"
echo ""

# Function to run wiggum with timeout
run_wiggum() {
    local timeout_sec=$DURATION_SECONDS

    # Remove any existing lock
    rm -f "$WIGGUM_HOME/.ralph/orchestrator/lock"

    # Run with timeout - creates should-exit file to signal shutdown
    # Create fake gh auth to bypass preflight check
    mkdir -p "$WIGGUM_HOME/.ralph/orchestrator"
    echo "logged_in" > "$WIGGUM_HOME/.ralph/orchestrator/.gh-auth-skip" 2>/dev/null || true

    timeout --signal=SIGINT --kill-after=5 "$timeout_sec" \
        "$WIGGUM_HOME/bin/wiggum" run \
        --mode local \
        --no-python \
        --max-workers "$MAX_WORKERS" \
        --no-resume \
        --no-fix \
        --no-merge \
        --no-sync \
        -q 2>&1 || true

    # Cleanup
    rm -f "$WIGGUM_HOME/.ralph/orchestrator/lock"
    rm -f "$WIGGUM_HOME/.ralph/orchestrator/should-exit"
}

case "${1:-stat}" in
    stat)
        echo "=== perf stat (basic counters) ==="
        perf stat -v \
            -e cycles,instructions,cache-references,cache-misses,branch-misses,task-clock,context-switches,cpu-migrations \
            -o "$RESULTS_DIR/perf-stat-${TIMESTAMP}.txt" \
            bash -c "$(declare -f run_wiggum); DURATION_SECONDS=$DURATION_SECONDS MAX_WORKERS=$MAX_WORKERS run_wiggum"

        echo ""
        echo "Results:"
        cat "$RESULTS_DIR/perf-stat-${TIMESTAMP}.txt"
        ;;

    record)
        echo "=== perf record (detailed profiling) ==="
        PERF_DATA="$RESULTS_DIR/perf-record-${TIMESTAMP}.data"

        # Use call-graph for function-level profiling
        perf record -g --call-graph dwarf \
            -o "$PERF_DATA" \
            -e cycles,cache-misses \
            -- bash -c "$(declare -f run_wiggum); DURATION_SECONDS=$DURATION_SECONDS MAX_WORKERS=$MAX_WORKERS run_wiggum"

        echo ""
        echo "=== perf report (top hotspots) ==="
        perf report -i "$PERF_DATA" --stdio --sort comm,dso,symbol 2>/dev/null | head -80

        echo ""
        echo "Data file: $PERF_DATA"
        echo "View with: perf report -i $PERF_DATA"
        ;;

    flame)
        echo "=== Flame graph generation ==="
        PERF_DATA="$RESULTS_DIR/perf-flame-${TIMESTAMP}.data"
        FLAME_SVG="$RESULTS_DIR/flame-${TIMESTAMP}.svg"

        perf record -g --call-graph dwarf \
            -o "$PERF_DATA" \
            -- bash -c "$(declare -f run_wiggum); DURATION_SECONDS=$DURATION_SECONDS MAX_WORKERS=$MAX_WORKERS run_wiggum"

        # Check for flame graph tools
        if command -v flamegraph.pl &>/dev/null; then
            perf script -i "$PERF_DATA" | stackcollapse-perf.pl | flamegraph.pl > "$FLAME_SVG"
            echo "Flame graph: $FLAME_SVG"
        elif command -v stackcollapse-perf.pl &>/dev/null; then
            perf script -i "$PERF_DATA" | stackcollapse-perf.pl | flamegraph.pl > "$FLAME_SVG"
            echo "Flame graph: $FLAME_SVG"
        else
            echo "Flame graph tools not found. Install from https://github.com/brendangregg/FlameGraph"
            echo ""
            echo "Manual generation:"
            echo "  perf script -i $PERF_DATA | stackcollapse-perf.pl | flamegraph.pl > $FLAME_SVG"
            echo ""
            echo "Alternative: use speedscope"
            echo "  perf script -i $PERF_DATA > $RESULTS_DIR/perf-script-${TIMESTAMP}.txt"
            echo "  speedscope $RESULTS_DIR/perf-script-${TIMESTAMP}.txt"
        fi
        ;;

    startup)
        echo "=== Startup time benchmark ==="
        # Measure just the initialization phase (sources all libs, validates project)
        for i in {1..5}; do
            echo "Run $i:"
            rm -f "$WIGGUM_HOME/.ralph/orchestrator/lock"

            # Time to first log line indicates startup complete
            START=$(date +%s.%N)
            timeout 3 "$WIGGUM_HOME/bin/wiggum" run --mode local --no-python -q 2>&1 || true
            END=$(date +%s.%N)

            ELAPSED=$(echo "$END - $START" | bc)
            echo "  Time: ${ELAPSED}s"

            rm -f "$WIGGUM_HOME/.ralph/orchestrator/lock"
            sleep 1
        done
        ;;

    *)
        echo "Unknown mode: $1"
        echo "Usage: $0 [stat|record|flame|startup]"
        exit 1
        ;;
esac

echo ""
echo "Benchmark complete."
