#!/usr/bin/env bash
# Callback: Log errors to central error log
# Runs from workspace dir: .ralph/workers/<worker_id>/workspace

MESSAGE="$1"

WORKER_DIR="$(dirname "$PWD")"
WORKER_ID="$(basename "$WORKER_DIR")"
RALPH_DIR="$(dirname "$(dirname "$WORKER_DIR")")"

[[ -n "$RALPH_DIR" ]] && mkdir -p "$RALPH_DIR/logs" 2>/dev/null || true

# Use flock to prevent interleaved writes from concurrent workers
LOG_FILE="$RALPH_DIR/logs/errors.log"
(
    flock -w 1 200 || { echo "[$(date -Iseconds)] ERROR: Worker $WORKER_ID: $MESSAGE" >> "$LOG_FILE"; exit 0; }
    echo "[$(date -Iseconds)] ERROR: Worker $WORKER_ID: $MESSAGE" >> "$LOG_FILE"
) 200>"${LOG_FILE}.lock"
