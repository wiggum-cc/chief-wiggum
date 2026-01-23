#!/usr/bin/env bash
# =============================================================================
# pipeline-loader.sh - Load pipeline JSON into parallel bash arrays
#
# Provides:
#   pipeline_load(file)              - Parse JSON, populate arrays, validate IDs
#   pipeline_resolve(project_dir, task_id, cli_pipeline_name) - Resolve config path
#   pipeline_find_step_index(step_id) - Return array index for a step ID
#   pipeline_step_count()            - Return number of steps
#
# After pipeline_load(), the following arrays are populated:
#   PIPELINE_STEP_IDS[i]
#   PIPELINE_STEP_AGENTS[i]
#   PIPELINE_STEP_BLOCKING[i]
#   PIPELINE_STEP_READONLY[i]
#   PIPELINE_STEP_ENABLED_BY[i]
#   PIPELINE_STEP_DEPENDS_ON[i]
#   PIPELINE_STEP_COMMIT_AFTER[i]
#   PIPELINE_STEP_CONFIG[i]        (JSON string)
#   PIPELINE_STEP_FIX_AGENT[i]
#   PIPELINE_STEP_FIX_MAX_ATTEMPTS[i]
#   PIPELINE_STEP_FIX_COMMIT_AFTER[i]
#   PIPELINE_STEP_HOOKS_PRE[i]     (JSON array string)
#   PIPELINE_STEP_HOOKS_POST[i]    (JSON array string)
# =============================================================================

# Prevent double-sourcing
[ -n "${_PIPELINE_LOADER_LOADED:-}" ] && return 0
_PIPELINE_LOADER_LOADED=1

# Pipeline arrays (global)
declare -a PIPELINE_STEP_IDS=()
declare -a PIPELINE_STEP_AGENTS=()
declare -a PIPELINE_STEP_BLOCKING=()
declare -a PIPELINE_STEP_READONLY=()
declare -a PIPELINE_STEP_ENABLED_BY=()
declare -a PIPELINE_STEP_DEPENDS_ON=()
declare -a PIPELINE_STEP_COMMIT_AFTER=()
declare -a PIPELINE_STEP_CONFIG=()
declare -a PIPELINE_STEP_FIX_AGENT=()
declare -a PIPELINE_STEP_FIX_MAX_ATTEMPTS=()
declare -a PIPELINE_STEP_FIX_COMMIT_AFTER=()
declare -a PIPELINE_STEP_HOOKS_PRE=()
declare -a PIPELINE_STEP_HOOKS_POST=()

# Pipeline metadata
PIPELINE_NAME=""

# Load pipeline configuration from a JSON file into parallel arrays
#
# Args:
#   file - Path to pipeline JSON file
#
# Returns: 0 on success, 1 on error
pipeline_load() {
    local file="$1"

    if [ ! -f "$file" ]; then
        log_error "Pipeline config not found: $file"
        return 1
    fi

    # Validate JSON
    if ! jq empty "$file" 2>/dev/null; then
        log_error "Invalid JSON in pipeline config: $file"
        return 1
    fi

    # Read pipeline name
    PIPELINE_NAME=$(jq -r '.name // "unnamed"' "$file")

    # Get step count
    local step_count
    step_count=$(jq '.steps | length' "$file")

    if [ "$step_count" -eq 0 ]; then
        log_error "Pipeline has no steps: $file"
        return 1
    fi

    # Clear arrays
    PIPELINE_STEP_IDS=()
    PIPELINE_STEP_AGENTS=()
    PIPELINE_STEP_BLOCKING=()
    PIPELINE_STEP_READONLY=()
    PIPELINE_STEP_ENABLED_BY=()
    PIPELINE_STEP_DEPENDS_ON=()
    PIPELINE_STEP_COMMIT_AFTER=()
    PIPELINE_STEP_CONFIG=()
    PIPELINE_STEP_FIX_AGENT=()
    PIPELINE_STEP_FIX_MAX_ATTEMPTS=()
    PIPELINE_STEP_FIX_COMMIT_AFTER=()
    PIPELINE_STEP_HOOKS_PRE=()
    PIPELINE_STEP_HOOKS_POST=()

    # Parse each step
    local i=0
    while [ "$i" -lt "$step_count" ]; do
        local step_json
        step_json=$(jq ".steps[$i]" "$file")

        PIPELINE_STEP_IDS+=("$(echo "$step_json" | jq -r '.id')")
        PIPELINE_STEP_AGENTS+=("$(echo "$step_json" | jq -r '.agent')")
        PIPELINE_STEP_BLOCKING+=("$(echo "$step_json" | jq -r '.blocking // true')")
        PIPELINE_STEP_READONLY+=("$(echo "$step_json" | jq -r '.readonly // false')")
        PIPELINE_STEP_ENABLED_BY+=("$(echo "$step_json" | jq -r '.enabled_by // ""')")
        PIPELINE_STEP_DEPENDS_ON+=("$(echo "$step_json" | jq -r '.depends_on // ""')")
        PIPELINE_STEP_COMMIT_AFTER+=("$(echo "$step_json" | jq -r '.commit_after // false')")
        PIPELINE_STEP_CONFIG+=("$(echo "$step_json" | jq -c '.config // {}')")
        PIPELINE_STEP_FIX_AGENT+=("$(echo "$step_json" | jq -r '.fix.agent // ""')")
        PIPELINE_STEP_FIX_MAX_ATTEMPTS+=("$(echo "$step_json" | jq -r '.fix.max_attempts // 2')")
        PIPELINE_STEP_FIX_COMMIT_AFTER+=("$(echo "$step_json" | jq -r '.fix.commit_after // true')")
        PIPELINE_STEP_HOOKS_PRE+=("$(echo "$step_json" | jq -c '.hooks.pre // []')")
        PIPELINE_STEP_HOOKS_POST+=("$(echo "$step_json" | jq -c '.hooks.post // []')")

        ((i++))
    done

    # Validate unique IDs
    local -A seen_ids
    for id in "${PIPELINE_STEP_IDS[@]}"; do
        if [ -z "$id" ] || [ "$id" = "null" ]; then
            log_error "Pipeline step missing required 'id' field"
            return 1
        fi
        if [ -n "${seen_ids[$id]:-}" ]; then
            log_error "Duplicate pipeline step ID: $id"
            return 1
        fi
        seen_ids["$id"]=1
    done

    # Validate agents are non-empty
    for agent in "${PIPELINE_STEP_AGENTS[@]}"; do
        if [ -z "$agent" ] || [ "$agent" = "null" ]; then
            log_error "Pipeline step missing required 'agent' field"
            return 1
        fi
    done

    # Validate depends_on references exist
    for dep in "${PIPELINE_STEP_DEPENDS_ON[@]}"; do
        if [ -n "$dep" ] && [ -z "${seen_ids[$dep]:-}" ]; then
            log_error "Pipeline step depends_on references unknown step: $dep"
            return 1
        fi
    done

    log "Loaded pipeline '$PIPELINE_NAME' with $step_count steps"
    return 0
}

# Load built-in defaults matching the hardcoded TASK_PIPELINE behavior
# Used as fallback when no pipeline config file exists
pipeline_load_builtin_defaults() {
    PIPELINE_NAME="builtin-default"

    PIPELINE_STEP_IDS=(planning execution summary audit test docs validation)
    PIPELINE_STEP_AGENTS=(plan-mode task-executor task-summarizer security-audit test-coverage documentation-writer validation-review)
    PIPELINE_STEP_BLOCKING=(false true false true true false true)
    PIPELINE_STEP_READONLY=(true false true true false false true)
    PIPELINE_STEP_ENABLED_BY=(WIGGUM_PLAN_MODE "" "" "" "" "" "")
    PIPELINE_STEP_DEPENDS_ON=("" "" execution "" "" "" "")
    PIPELINE_STEP_COMMIT_AFTER=(false false false false true true false)
    PIPELINE_STEP_CONFIG=('{}' '{"max_iterations":20,"max_turns":50,"supervisor_interval":2}' '{}' '{}' '{}' '{}' '{}')
    PIPELINE_STEP_FIX_AGENT=("" "" "" security-fix "" "" "")
    PIPELINE_STEP_FIX_MAX_ATTEMPTS=(2 2 2 2 2 2 2)
    PIPELINE_STEP_FIX_COMMIT_AFTER=(true true true true true true true)
    PIPELINE_STEP_HOOKS_PRE=('[]' '[]' '[]' '[]' '[]' '[]' '["stop_violation_monitor \"$VIOLATION_MONITOR_PID\""]')
    PIPELINE_STEP_HOOKS_POST=('[]' '[]' '[]' '[]' '[]' '[]' '[]')

    log "Loaded built-in default pipeline with ${#PIPELINE_STEP_IDS[@]} steps"
}

# Resolve the pipeline config file path using priority order:
#   1. CLI flag (--pipeline <name>) -> config/pipelines/<name>.json or .ralph/pipelines/<name>.json
#   2. Per-task override -> .ralph/pipelines/<task-id>.json
#   3. Project default -> config/pipeline.json
#   4. Built-in fallback (returns empty string, caller uses pipeline_load_builtin_defaults)
#
# Args:
#   project_dir       - Project root directory
#   task_id           - Task ID (e.g., TASK-001)
#   cli_pipeline_name - Pipeline name from --pipeline flag (can be empty)
#
# Returns: Path to pipeline config file (stdout), or empty string for builtin
pipeline_resolve() {
    local project_dir="$1"
    local task_id="$2"
    local cli_pipeline_name="${3:-}"

    # 1. CLI flag: --pipeline <name>
    if [ -n "$cli_pipeline_name" ]; then
        # Check project config/pipelines/ first
        local cli_path="$WIGGUM_HOME/config/pipelines/${cli_pipeline_name}.json"
        if [ -f "$cli_path" ]; then
            echo "$cli_path"
            return 0
        fi
        # Check .ralph/pipelines/
        cli_path="$project_dir/.ralph/pipelines/${cli_pipeline_name}.json"
        if [ -f "$cli_path" ]; then
            echo "$cli_path"
            return 0
        fi
        log_warn "Pipeline '$cli_pipeline_name' not found, falling back to defaults"
    fi

    # 2. Per-task override
    local task_path="$project_dir/.ralph/pipelines/${task_id}.json"
    if [ -f "$task_path" ]; then
        echo "$task_path"
        return 0
    fi

    # 3. Project default
    local default_path="$WIGGUM_HOME/config/pipeline.json"
    if [ -f "$default_path" ]; then
        echo "$default_path"
        return 0
    fi

    # 4. No config found - return empty (caller will use builtin defaults)
    echo ""
    return 0
}

# Find the array index for a given step ID
#
# Args:
#   step_id - The step ID to find
#
# Returns: Array index (0-based) via stdout, or -1 if not found
pipeline_find_step_index() {
    local step_id="$1"
    local i=0

    for id in "${PIPELINE_STEP_IDS[@]}"; do
        if [ "$id" = "$step_id" ]; then
            echo "$i"
            return 0
        fi
        ((i++))
    done

    echo "-1"
    return 1
}

# Get the number of steps in the loaded pipeline
pipeline_step_count() {
    echo "${#PIPELINE_STEP_IDS[@]}"
}
