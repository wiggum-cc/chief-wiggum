#!/usr/bin/env bash
# =============================================================================
# agent-result.sh - Structured agent results and communication protocol
#
# Provides:
#   - Structured agent results (epoch-named JSON files)
#   - Result validation and schema checking
#   - Agent communication protocol
#   - Unified result extraction and writing
#
# Split from agent-base.sh for maintainability.
# =============================================================================
set -euo pipefail

[ -n "${_AGENT_RESULT_LOADED:-}" ] && return 0
_AGENT_RESULT_LOADED=1

[ -z "${_WIGGUM_SRC_PLATFORM_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/safe-path.sh"

# =============================================================================
# STRUCTURED AGENT RESULTS (Epoch-Named)
# =============================================================================
# Results are written to: results/<epoch>-<agent-type>-result.json
# Reports are written to: reports/<epoch>-<agent-type>-report.md
#
# Schema:
# {
#   "agent_type": "engineering.security-audit",
#   "status": "success|failure|partial|unknown",
#   "exit_code": 0,
#   "started_at": "2024-01-15T10:30:00Z",
#   "completed_at": "2024-01-15T10:45:00Z",
#   "duration_seconds": 900,
#   "task_id": "TASK-001",
#   "worker_id": "worker-TASK-001-abc123",
#   "iterations_completed": 3,
#   "outputs": {
#     "gate_result": "PASS"
#   },
#   "errors": [],
#   "metadata": {}
# }

# Validate agent result file against expected schema
#
# Checks:
#   - agent_type is non-empty string
#   - status is one of: success, failure, partial, unknown
#   - exit_code is integer
#   - outputs.gate_result (if present) matches [A-Z]{3,10}
#
# Args:
#   result_file - Path to the result JSON file
#
# Returns: 0 if valid, 1 if invalid (logs specific errors)
validate_result_schema() {
    local result_file="$1"

    if [ ! -f "$result_file" ]; then
        log_error "Result schema validation: file not found: $result_file"
        return 1
    fi

    local errors=0

    # Check agent_type is non-empty
    local agent_type
    agent_type=$(jq -r '.agent_type // ""' "$result_file" 2>/dev/null)
    if [ -z "$agent_type" ] || [ "$agent_type" = "null" ]; then
        log_error "Result schema: 'agent_type' is missing or empty in $(basename "$result_file")"
        errors=1
    fi

    # Check status is valid enum
    local status
    status=$(jq -r '.status // ""' "$result_file" 2>/dev/null)
    case "$status" in
        success|failure|partial|unknown) ;;
        *)
            log_error "Result schema: 'status' is invalid ('$status') in $(basename "$result_file") - expected success|failure|partial|unknown"
            errors=1
            ;;
    esac

    # Check exit_code is integer
    local exit_code
    exit_code=$(jq -r '.exit_code // ""' "$result_file" 2>/dev/null)
    if ! [[ "$exit_code" =~ ^[0-9]+$ ]]; then
        log_error "Result schema: 'exit_code' is not an integer ('$exit_code') in $(basename "$result_file")"
        errors=1
    fi

    # Check outputs.gate_result if present (must match [A-Z]{3,10})
    local gate_result
    gate_result=$(jq -r '.outputs.gate_result // empty' "$result_file" 2>/dev/null)
    if [ -n "$gate_result" ]; then
        if ! [[ "$gate_result" =~ ^[A-Z]{3,10}$ ]]; then
            log_error "Result schema: 'outputs.gate_result' is invalid ('$gate_result') in $(basename "$result_file") - must match [A-Z]{3,10}"
            errors=1
        fi
    fi

    return $errors
}

# Get the epoch-named result file path for the current agent
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: Path like results/<epoch>-<agent-type>-result.json
agent_get_result_path() {
    local worker_dir="$1"
    local epoch="${_AGENT_START_EPOCH:-$(epoch_now)}"
    local name="${WIGGUM_STEP_ID:-${AGENT_TYPE:-unknown}}"
    echo "$worker_dir/results/${epoch}-${name}-result.json"
}

# Find the latest result file for a given agent type
#
# Args:
#   worker_dir - Worker directory path
#   agent_name - Agent type name (e.g., "engineering.security-audit")
#
# Returns: Path to the latest result JSON file, or empty string
agent_find_latest_result() {
    local worker_dir="$1"
    local agent_name="$2"

    # Use find_newest for portable mtime sorting (handles filenames with spaces)
    find_newest "$worker_dir/results" -maxdepth 1 -name "*-${agent_name}-result.json"
}

# Find the latest report file for a given agent type
#
# Args:
#   worker_dir - Worker directory path
#   agent_name - Agent type name (e.g., "engineering.security-audit")
#
# Returns: Path to the latest report MD file, or empty string
agent_find_latest_report() {
    local worker_dir="$1"
    local agent_name="$2"

    # Use find_newest for portable mtime sorting (handles filenames with spaces)
    find_newest "$worker_dir/reports" -maxdepth 1 -name "*-${agent_name}-report.md"
}

# Write a report file with epoch naming
#
# Args:
#   worker_dir - Worker directory path
#   content    - Report content to write
#
# Returns: Path to the written report file (via stdout)
agent_write_report() {
    local worker_dir="$1"
    safe_path "$worker_dir" "worker_dir" || return 1
    local content="$2"
    local epoch="${_AGENT_START_EPOCH:-$(epoch_now)}"
    local name="${WIGGUM_STEP_ID:-${AGENT_TYPE:-unknown}}"
    local report_path="$worker_dir/reports/${epoch}-${name}-report.md"

    mkdir -p "$worker_dir/reports"
    echo "$content" > "$report_path"
    echo "$report_path"
}

# Write agent result to epoch-named JSON file
#
# Args:
#   worker_dir    - Worker directory path
#   gate_result   - Gate result: PASS, FAIL, FIX, SKIP
#   extra_outputs - JSON object string of additional output values (optional)
#   errors        - JSON array string of error messages (optional)
#
# The function automatically derives status and exit_code from gate_result:
#   PASS/SKIP -> status=success, exit_code=0
#   FAIL      -> status=failure, exit_code=10
#   FIX       -> status=partial, exit_code=0
#   other     -> status=unknown, exit_code=1
agent_write_result() {
    local worker_dir="$1"
    safe_path "$worker_dir" "worker_dir" || return 1
    local gate_result="$2"
    local extra_outputs="${3:-'{}'}"
    local errors="${4:-'[]'}"

    # Set defaults for optional JSON params
    [ -z "$extra_outputs" ] || [ "$extra_outputs" = "'{}'" ] && extra_outputs='{}'
    [ -z "$errors" ] || [ "$errors" = "'[]'" ] && errors='[]'

    # Derive status and exit_code from gate_result using config-driven mappings
    [ -z "${_RESULT_MAPPINGS_LOADED:-}" ] && load_result_mappings
    local result_status exit_code
    result_status=$(get_result_status "$gate_result")
    exit_code=$(get_result_exit_code "$gate_result")

    # Merge gate_result into outputs
    local outputs
    if [ "$extra_outputs" != "{}" ] && [ -n "$extra_outputs" ]; then
        outputs=$(echo "$extra_outputs" | jq -c --arg gr "$gate_result" '. + {gate_result: $gr}')
    else
        outputs="{\"gate_result\":\"$gate_result\"}"
    fi

    local metadata='{}'

    mkdir -p "$worker_dir/results"
    local result_file
    result_file=$(agent_get_result_path "$worker_dir")

    local worker_id task_id
    worker_id=$(basename "$worker_dir")
    task_id="${_AGENT_TASK_ID:-unknown}"

    # Get timing info from epoch tracking
    local started_at completed_at duration_seconds
    completed_at=$(iso_now)
    duration_seconds=0
    started_at="$completed_at"

    if [ -n "${_AGENT_START_EPOCH:-}" ] && [[ "${_AGENT_START_EPOCH}" =~ ^[0-9]+$ ]]; then
        started_at=$(iso_from_epoch "$_AGENT_START_EPOCH")
        duration_seconds=$(($(epoch_now) - _AGENT_START_EPOCH))
    elif [ -f "$worker_dir/worker.log" ]; then
        local start_epoch
        start_epoch=$(grep "AGENT_STARTED" "$worker_dir/worker.log" 2>/dev/null | tail -1 | grep_pcre_match 'start_time=\K\d+' || true)
        if [ -n "$start_epoch" ] && [[ "$start_epoch" =~ ^[0-9]+$ ]]; then
            started_at=$(iso_from_epoch "$start_epoch")
            duration_seconds=$(($(epoch_now) - start_epoch))
        fi
    fi

    # Get iterations from logs directory
    local iterations_completed=0
    if [ -d "$worker_dir/logs" ]; then
        local count
        # Count all agent log files (any step ID prefix, excluding summaries)
        count=$(find "$worker_dir/logs" -name "*.log" ! -name "*summary*" 2>/dev/null | wc -l || true)
        iterations_completed=$(echo "$count" | tr -d '[:space:]')
    fi
    # Ensure numeric values
    [[ "$iterations_completed" =~ ^[0-9]+$ ]] || iterations_completed=0
    [[ "$duration_seconds" =~ ^[0-9]+$ ]] || duration_seconds=0
    [[ "$exit_code" =~ ^[0-9]+$ ]] || exit_code=1

    # Build JSON result using a heredoc to avoid quoting issues
    cat > "$result_file" << JSONEOF
{
  "agent_type": "${AGENT_TYPE:-unknown}",
  "status": "$result_status",
  "exit_code": $exit_code,
  "started_at": "$started_at",
  "completed_at": "$completed_at",
  "duration_seconds": $duration_seconds,
  "task_id": "$task_id",
  "worker_id": "$worker_id",
  "iterations_completed": $iterations_completed,
  "outputs": $outputs,
  "errors": $errors,
  "metadata": $metadata
}
JSONEOF
}

# Read agent result from the latest result JSON file
#
# Args:
#   worker_dir - Worker directory path
#   field      - Optional: specific field to extract (uses jq path syntax)
#
# Returns: Full JSON or specific field value
agent_read_result() {
    local worker_dir="$1"
    local field="${2:-}"

    local agent_type="${AGENT_TYPE:-unknown}"
    local result_file
    result_file=$(agent_find_latest_result "$worker_dir" "$agent_type")

    if [ -z "$result_file" ] || [ ! -f "$result_file" ]; then
        echo ""
        return 1
    fi

    if [ -n "$field" ]; then
        jq -r "$field // empty" "$result_file" 2>/dev/null
    else
        cat "$result_file"
    fi
}

# Check if agent result indicates success
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: 0 if success, 1 otherwise
agent_result_is_success() {
    local worker_dir="$1"
    local status
    status=$(agent_read_result "$worker_dir" ".status")
    [ "$status" = "success" ]
}

# Get specific output value from agent result
#
# Args:
#   worker_dir - Worker directory path
#   key        - Output key to retrieve
#
# Returns: Output value or empty string
agent_get_output() {
    local worker_dir="$1"
    local key="$2"

    local agent_type="${AGENT_TYPE:-unknown}"
    local result_file
    result_file=$(agent_find_latest_result "$worker_dir" "$agent_type")

    if [ -n "$result_file" ] && [ -f "$result_file" ]; then
        jq -r ".outputs.$key // empty" "$result_file" 2>/dev/null
    fi
}

# Set a single output value in existing result
#
# Args:
#   worker_dir - Worker directory path
#   key        - Output key
#   value      - Output value
agent_set_output() {
    local worker_dir="$1"
    local key="$2"
    local value="$3"

    local agent_type="${AGENT_TYPE:-unknown}"
    local result_file
    result_file=$(agent_find_latest_result "$worker_dir" "$agent_type")

    if [ -n "$result_file" ] && [ -f "$result_file" ]; then
        local tmp_file
        tmp_file=$(agent_mktemp "$worker_dir")
        jq --arg key "$key" --arg value "$value" '.outputs[$key] = $value' "$result_file" > "$tmp_file"
        mv "$tmp_file" "$result_file"
    fi
}

# Add error to agent result
#
# Args:
#   worker_dir - Worker directory path
#   error_msg  - Error message to add
agent_add_error() {
    local worker_dir="$1"
    local error_msg="$2"

    local agent_type="${AGENT_TYPE:-unknown}"
    local result_file
    result_file=$(agent_find_latest_result "$worker_dir" "$agent_type")

    if [ -n "$result_file" ] && [ -f "$result_file" ]; then
        local tmp_file
        tmp_file=$(agent_mktemp "$worker_dir")
        jq --arg err "$error_msg" '.errors += [$err]' "$result_file" > "$tmp_file"
        mv "$tmp_file" "$result_file"
    fi
}

# =============================================================================
# AGENT COMMUNICATION PROTOCOL
# =============================================================================
# Standard file paths for inter-agent communication.
# Results and reports use epoch-named files in results/ and reports/ directories.

# Get the standard path for a communication file
#
# Args:
#   worker_dir - Worker directory path
#   file_type  - Type of file: result, report, comments, summary, prd, workspace
#
# Returns: Full path to the file
agent_comm_path() {
    local worker_dir="$1"
    local file_type="$2"

    case "$file_type" in
        result)
            agent_find_latest_result "$worker_dir" "${AGENT_TYPE:-unknown}"
            ;;
        report)
            agent_find_latest_report "$worker_dir" "${AGENT_TYPE:-unknown}"
            ;;
        comments)
            echo "$worker_dir/task-comments.md"
            ;;
        summary)
            echo "$worker_dir/summaries/summary.txt"
            ;;
        prd)
            echo "$worker_dir/prd.md"
            ;;
        workspace)
            echo "$worker_dir/workspace"
            ;;
        *)
            echo "$worker_dir/$file_type"
            ;;
    esac
}

# Check if a communication file exists and is non-empty
#
# Args:
#   worker_dir - Worker directory path
#   file_type  - Type of file
#
# Returns: 0 if exists and non-empty, 1 otherwise
agent_comm_exists() {
    local worker_dir="$1"
    local file_type="$2"
    local path
    path=$(agent_comm_path "$worker_dir" "$file_type")

    [ -n "$path" ] && [ -e "$path" ] && [ -s "$path" ]
}

# =============================================================================
# UNIFIED RESULT EXTRACTION AND WRITING
# =============================================================================

# Extract results from log files and write to epoch-named result/report files
# This is the unified function that replaces per-agent extraction logic
#
# Args:
#   worker_dir    - Worker directory path
#   agent_name    - Agent name for logging (e.g., "VALIDATION", "SECURITY")
#   log_prefix    - Log file prefix (e.g., "validation", "audit", "test")
#   report_tag    - XML tag name for report content (e.g., "review", "report")
#   valid_values  - Pipe-separated valid result values (e.g., "PASS|FAIL")
#
# Returns: Sets global variable ${agent_name}_RESULT (e.g., VALIDATION_RESULT)
agent_extract_and_write_result() {
    local worker_dir="$1"
    local agent_name="$2"
    local log_prefix="$3"
    local report_tag="$4"
    local valid_values="$5"

    local result="UNKNOWN"
    local report_rel=""

    # Find the latest log file for this step (run-isolated via RALPH_RUN_ID)
    # RALPH_RUN_ID format: {step_id}-{epoch}, matching log dir naming
    # Pattern matches both old format (prefix-N.log) and new format (prefix-N-timestamp.log)
    local log_file=""
    local run_id="${RALPH_RUN_ID:-}"
    if [ -n "$run_id" ] && [ -d "$worker_dir/logs/$run_id" ]; then
        log_file=$(find_newest "$worker_dir/logs/$run_id" -name "${log_prefix}-*.log")
    fi

    if [ -n "$log_file" ] && [ -f "$log_file" ]; then
        # Extract report content and save using agent_write_report
        local report_content
        report_content=$(_extract_tag_content_from_stream_json "$log_file" "$report_tag") || true

        if [ -n "$report_content" ]; then
            local report_path
            report_path=$(agent_write_report "$worker_dir" "$report_content")
            report_rel="$report_path"
            case "$report_path" in
                "$worker_dir"/*) report_rel="${report_path#"$worker_dir"/}" ;;
            esac
            log "${agent_name} report saved to $(basename "$report_path")"
        fi

        # Extract result value (LAST occurrence to avoid matching examples in prompts)
        result=$(_extract_result_value_from_stream_json "$log_file" "$valid_values") || true
        if [ -z "$result" ]; then
            result="UNKNOWN"
        fi
    fi

    # Get session_id for output and potential backup extraction
    local session_id="${RALPH_LOOP_LAST_SESSION_ID:-}"
    if [ -z "$session_id" ] && [ -n "$log_file" ] && [ -f "$log_file" ]; then
        session_id=$(_extract_session_id_from_log "$log_file")
    fi

    # Backup extraction if result is UNKNOWN and session_id is available
    if [ "$result" = "UNKNOWN" ] && [ -n "$session_id" ]; then
        local backup_enabled="${WIGGUM_RESULT_BACKUP_ENABLED:-true}"
        if [ "$backup_enabled" = "true" ]; then
            log "Result UNKNOWN - attempting backup extraction via session resume"
            local backup_result
            backup_result=$(_backup_result_extraction "$session_id" "$valid_values" "$worker_dir" "$log_prefix")
            if [ -n "$backup_result" ] && [ "$backup_result" != "UNKNOWN" ]; then
                result="$backup_result"
                log "Backup extraction recovered result: $result"
            else
                log_warn "Backup extraction failed - result remains UNKNOWN"
            fi
        fi
    fi

    # Build extra_outputs for downstream steps. Keep report paths relative to
    # worker_dir so markdown prompts can reference them from workspace via @../.
    local extra_outputs
    extra_outputs=$(jq -cn \
        --arg session "$session_id" \
        --arg report "$report_rel" \
        --arg parent_report "${WIGGUM_PARENT_REPORT:-}" \
        '{}
         + (if $session != "" then {session_id: $session} else {} end)
         + (if $report != "" then {report_file: $report} else {} end)
         + (if $parent_report != "" then {parent_report_file: $parent_report} else {} end)')

    # Write epoch-named result JSON with gate_result and session_id
    agent_write_result "$worker_dir" "$result" "$extra_outputs"

    # Set global variable for the calling agent (sanitize name: hyphens -> underscores)
    local var_name="${agent_name//-/_}_RESULT"
    printf -v "$var_name" '%s' "$result"

    log "${agent_name} result: $result"
}

# Read a sub-agent's gate_result from its latest epoch-named result file
#
# Args:
#   worker_dir  - Worker directory path
#   agent_name  - Agent type name (e.g., "engineering.security-audit")
#
# Returns: gate_result value ([A-Z]{3,10}) or "UNKNOWN"
agent_read_subagent_result() {
    local worker_dir="$1"
    local agent_name="$2"

    local result=""
    local result_file
    result_file=$(agent_find_latest_result "$worker_dir" "$agent_name")

    if [ -n "$result_file" ] && [ -f "$result_file" ]; then
        result=$(jq -r '.outputs.gate_result // empty' "$result_file" 2>/dev/null)
    fi

    # Default to UNKNOWN
    if [ -z "$result" ]; then
        result="UNKNOWN"
    fi

    echo "$result"
}

# Read a pipeline step's gate_result from its step-ID-named result file
#
# Args:
#   worker_dir - Worker directory path
#   step_id    - Pipeline step ID (e.g., "audit", "execution")
#
# Returns: gate_result value ([A-Z]{3,10}) or "UNKNOWN"
agent_read_step_result() {
    local worker_dir="$1"
    local step_id="$2"

    local result=""
    local result_file
    result_file=$(agent_find_latest_result "$worker_dir" "$step_id")

    if [ -n "$result_file" ] && [ -f "$result_file" ]; then
        result=$(jq -r '.outputs.gate_result // empty' "$result_file" 2>/dev/null)
    fi

    if [ -z "$result" ]; then
        result="UNKNOWN"
    fi

    echo "$result"
}
