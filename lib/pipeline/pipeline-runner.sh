#!/usr/bin/env bash
# =============================================================================
# pipeline-runner.sh - Execute pipeline steps sequentially
#
# Provides:
#   pipeline_run_all(worker_dir, project_dir, workspace, start_from_step)
#
# Requires:
#   - pipeline-loader.sh sourced and pipeline loaded
#   - agent-base.sh sourced (for run_sub_agent, agent_read_subagent_result, etc.)
#   - _phase_start/_phase_end/_commit_subagent_changes from task-worker.sh
#   - PIPELINE_PLAN_FILE, PIPELINE_RESUME_INSTRUCTIONS exported by caller
# =============================================================================

# Prevent double-sourcing
[ -n "${_PIPELINE_RUNNER_LOADED:-}" ] && return 0
_PIPELINE_RUNNER_LOADED=1

# Run all pipeline steps from start_from_step onward
#
# Args:
#   worker_dir      - Worker directory path
#   project_dir     - Project root directory
#   workspace       - Workspace directory (git worktree)
#   start_from_step - Step ID to start from (empty = first step)
#
# Returns: 0 on success, 1 if a blocking step failed
pipeline_run_all() {
    local worker_dir="$1"
    local project_dir="$2"
    local workspace="$3"
    local start_from_step="${4:-}"

    local step_count
    step_count=$(pipeline_step_count)
    local start_idx=0

    # Resolve start_from_step to index
    if [ -n "$start_from_step" ]; then
        local resolved_idx
        resolved_idx=$(pipeline_find_step_index "$start_from_step")
        if [ "$resolved_idx" -ge 0 ]; then
            start_idx="$resolved_idx"
        else
            log_warn "Unknown start_from_step '$start_from_step' - starting from beginning"
        fi
    fi

    local i="$start_idx"
    while [ "$i" -lt "$step_count" ]; do
        local step_id="${PIPELINE_STEP_IDS[$i]}"

        # Check enabled_by condition
        local enabled_by="${PIPELINE_STEP_ENABLED_BY[$i]}"
        if [ -n "$enabled_by" ]; then
            local env_val="${!enabled_by:-}"
            if [ "$env_val" != "true" ]; then
                log_debug "Skipping step '$step_id' (enabled_by=$enabled_by is not 'true')"
                ((i++))
                continue
            fi
        fi

        # Check depends_on condition
        local depends_on="${PIPELINE_STEP_DEPENDS_ON[$i]}"
        if [ -n "$depends_on" ]; then
            local dep_result
            dep_result=$(agent_read_step_result "$worker_dir" "$depends_on")
            if [ "$dep_result" = "FAIL" ] || [ "$dep_result" = "UNKNOWN" ]; then
                log "Skipping step '$step_id' (depends_on '$depends_on' result: $dep_result)"
                ((i++))
                continue
            fi
        fi

        # Check workspace still exists
        if [ ! -d "$workspace" ]; then
            log_error "Workspace no longer exists, aborting pipeline at step '$step_id'"
            return 1
        fi

        # Run the step
        if ! _pipeline_run_step "$i" "$worker_dir" "$project_dir" "$workspace"; then
            local blocking="${PIPELINE_STEP_BLOCKING[$i]}"
            if [ "$blocking" = "true" ]; then
                log_error "Blocking step '$step_id' failed - halting pipeline"
                return 1
            fi
        fi

        ((i++))
    done

    return 0
}

# Run a single pipeline step
#
# Args:
#   idx         - Step index in pipeline arrays
#   worker_dir  - Worker directory path
#   project_dir - Project root directory
#   workspace   - Workspace directory
#
# Returns: 0 on success/non-blocking-failure, 1 on blocking failure
_pipeline_run_step() {
    local idx="$1"
    local worker_dir="$2"
    local project_dir="$3"
    local workspace="$4"

    local step_id="${PIPELINE_STEP_IDS[$idx]}"
    local step_agent="${PIPELINE_STEP_AGENTS[$idx]}"
    local blocking="${PIPELINE_STEP_BLOCKING[$idx]}"
    local readonly="${PIPELINE_STEP_READONLY[$idx]}"
    local commit_after="${PIPELINE_STEP_COMMIT_AFTER[$idx]}"

    log "Running pipeline step: $step_id (agent=$step_agent, blocking=$blocking, readonly=$readonly)"

    # Track phase timing
    _phase_start "$step_id"

    # Export step ID for result file naming
    export WIGGUM_STEP_ID="$step_id"

    # Write step config
    _write_step_config "$worker_dir" "$idx"

    # Special handling for task-executor: write executor-config.json
    if [ "$step_agent" = "task-executor" ]; then
        _prepare_executor_config "$worker_dir" "$idx"
    fi

    # Run pre-hooks
    _run_step_hooks "pre" "$idx" "$worker_dir" "$project_dir" "$workspace"

    # Readonly stash
    if [ "$readonly" = "true" ]; then
        _readonly_stash "$workspace" "$step_id"
    fi

    # Run the agent
    run_sub_agent "$step_agent" "$worker_dir" "$project_dir"
    local agent_exit=$?

    # Readonly pop
    if [ "$readonly" = "true" ]; then
        _readonly_pop "$workspace" "$step_id"
    fi

    # Read the step result
    local gate_result
    gate_result=$(agent_read_step_result "$worker_dir" "$step_id")
    log "Step '$step_id' result: $gate_result (exit: $agent_exit)"

    # Run post-hooks
    _run_step_hooks "post" "$idx" "$worker_dir" "$project_dir" "$workspace"

    # Handle FIX result
    if [ "$gate_result" = "FIX" ]; then
        local fix_agent="${PIPELINE_STEP_FIX_AGENT[$idx]}"
        if [ -n "$fix_agent" ]; then
            if _handle_fix_retry "$idx" "$worker_dir" "$project_dir" "$workspace"; then
                gate_result="PASS"
            else
                # Fix failed - check if blocking
                if [ "$blocking" = "true" ]; then
                    _phase_end "$step_id"
                    unset WIGGUM_STEP_ID
                    return 1
                fi
            fi
        else
            # No fix agent configured, treat FIX as failure for blocking
            if [ "$blocking" = "true" ]; then
                log_error "Step '$step_id' returned FIX but no fix agent configured"
                _phase_end "$step_id"
                unset WIGGUM_STEP_ID
                return 1
            fi
        fi
    fi

    # Handle FAIL/STOP
    if [ "$gate_result" = "FAIL" ] || [ "$gate_result" = "STOP" ]; then
        if [ "$blocking" = "true" ]; then
            _phase_end "$step_id"
            unset WIGGUM_STEP_ID
            return 1
        fi
    fi

    # Commit changes if configured (and not readonly)
    if [ "$commit_after" = "true" ] && [ "$readonly" != "true" ]; then
        _commit_subagent_changes "$workspace" "$step_agent"
    fi

    _phase_end "$step_id"
    unset WIGGUM_STEP_ID
    return 0
}

# Handle FIX retry loop: run fix agent, re-verify, up to max_attempts
#
# Args:
#   idx         - Step index
#   worker_dir  - Worker directory
#   project_dir - Project directory
#   workspace   - Workspace directory
#
# Returns: 0 if fix succeeded (PASS on re-verify), 1 if exhausted
_handle_fix_retry() {
    local idx="$1"
    local worker_dir="$2"
    local project_dir="$3"
    local workspace="$4"

    local step_id="${PIPELINE_STEP_IDS[$idx]}"
    local step_agent="${PIPELINE_STEP_AGENTS[$idx]}"
    local readonly="${PIPELINE_STEP_READONLY[$idx]}"
    local fix_agent="${PIPELINE_STEP_FIX_AGENT[$idx]}"
    local max_attempts="${PIPELINE_STEP_FIX_MAX_ATTEMPTS[$idx]}"
    local fix_commit="${PIPELINE_STEP_FIX_COMMIT_AFTER[$idx]}"

    local attempt=1
    while [ $attempt -le "$max_attempts" ]; do
        log "Fix attempt $attempt/$max_attempts for step '$step_id' using agent '$fix_agent'"

        # Run fix agent (never readonly - it must modify files)
        export WIGGUM_STEP_ID="${step_id}-fix-${attempt}"
        run_sub_agent "$fix_agent" "$worker_dir" "$project_dir"

        # Commit fix changes
        if [ "$fix_commit" = "true" ]; then
            _commit_subagent_changes "$workspace" "$fix_agent"
        fi

        # Re-run original agent to verify
        local verify_id="${step_id}-verify-${attempt}"
        export WIGGUM_STEP_ID="$verify_id"

        # Apply readonly for verification if the step is readonly
        if [ "$readonly" = "true" ]; then
            _readonly_stash "$workspace" "$verify_id"
        fi

        run_sub_agent "$step_agent" "$worker_dir" "$project_dir"

        if [ "$readonly" = "true" ]; then
            _readonly_pop "$workspace" "$verify_id"
        fi

        # Check verification result
        local verify_result
        verify_result=$(agent_read_step_result "$worker_dir" "$verify_id")
        log "Verify attempt $attempt result: $verify_result"

        if [ "$verify_result" = "PASS" ]; then
            # Promote verify result to canonical step_id
            log "Fix verified successfully for step '$step_id'"
            export WIGGUM_STEP_ID="$step_id"
            return 0
        elif [ "$verify_result" = "FAIL" ] || [ "$verify_result" = "STOP" ]; then
            log_error "Verification returned $verify_result after fix - halting retry"
            export WIGGUM_STEP_ID="$step_id"
            return 1
        fi

        # Still FIX - try again
        ((attempt++))
    done

    log_error "Fix retry exhausted ($max_attempts attempts) for step '$step_id'"
    export WIGGUM_STEP_ID="$step_id"
    return 1
}

# Execute pre or post hook commands for a step
#
# Args:
#   phase       - "pre" or "post"
#   idx         - Step index
#   worker_dir  - Worker directory
#   project_dir - Project directory
#   workspace   - Workspace directory
_run_step_hooks() {
    local phase="$1"
    local idx="$2"
    local worker_dir="$3"
    local project_dir="$4"
    local workspace="$5"

    local hooks_json
    if [ "$phase" = "pre" ]; then
        hooks_json="${PIPELINE_STEP_HOOKS_PRE[$idx]}"
    else
        hooks_json="${PIPELINE_STEP_HOOKS_POST[$idx]}"
    fi

    # Skip if empty array
    if [ "$hooks_json" = "[]" ] || [ -z "$hooks_json" ]; then
        return 0
    fi

    local hook_count
    hook_count=$(echo "$hooks_json" | jq 'length')

    local h=0
    while [ "$h" -lt "$hook_count" ]; do
        local cmd
        cmd=$(echo "$hooks_json" | jq -r ".[$h]")

        log_debug "Running $phase hook for step '${PIPELINE_STEP_IDS[$idx]}': $cmd"

        # Execute hook in subshell with context variables available
        (
            export PIPELINE_WORKER_DIR="$worker_dir"
            export PIPELINE_PROJECT_DIR="$project_dir"
            export PIPELINE_WORKSPACE="$workspace"
            export PIPELINE_STEP_ID="${PIPELINE_STEP_IDS[$idx]}"
            cd "$workspace" 2>/dev/null || true
            eval "$cmd"
        ) || log_warn "$phase hook failed for step '${PIPELINE_STEP_IDS[$idx]}': $cmd"

        ((h++))
    done
}

# Write step-config.json for the current step
#
# Args:
#   worker_dir - Worker directory
#   idx        - Step index
_write_step_config() {
    local worker_dir="$1"
    local idx="$2"

    local config_json="${PIPELINE_STEP_CONFIG[$idx]}"
    echo "$config_json" > "$worker_dir/step-config.json"
}

# Special case: prepare executor-config.json for task-executor
# Merges step config with PIPELINE_PLAN_FILE and PIPELINE_RESUME_INSTRUCTIONS
#
# Args:
#   worker_dir - Worker directory
#   idx        - Step index
_prepare_executor_config() {
    local worker_dir="$1"
    local idx="$2"

    local config_json="${PIPELINE_STEP_CONFIG[$idx]}"

    # Extract values from step config with defaults
    local max_iterations max_turns supervisor_interval
    max_iterations=$(echo "$config_json" | jq -r '.max_iterations // 20')
    max_turns=$(echo "$config_json" | jq -r '.max_turns // 50')
    supervisor_interval=$(echo "$config_json" | jq -r '.supervisor_interval // 2')

    local plan_file="${PIPELINE_PLAN_FILE:-}"
    local resume_instructions="${PIPELINE_RESUME_INSTRUCTIONS:-}"

    jq -n \
        --argjson max_iterations "$max_iterations" \
        --argjson max_turns "$max_turns" \
        --argjson supervisor_interval "$supervisor_interval" \
        --arg plan_file "$plan_file" \
        --arg resume_instructions "$resume_instructions" \
        '{
            max_iterations: $max_iterations,
            max_turns: $max_turns,
            supervisor_interval: $supervisor_interval,
            plan_file: $plan_file,
            resume_instructions: $resume_instructions
        }' > "$worker_dir/executor-config.json"
}

# Stash workspace changes before a readonly agent
#
# Args:
#   workspace - Workspace directory
#   step_id   - Step ID (for stash message)
_readonly_stash() {
    local workspace="$1"
    local step_id="$2"

    cd "$workspace" 2>/dev/null || return 0
    git stash --include-untracked -m "pipeline-readonly-$step_id" 2>/dev/null || true
}

# Pop stashed changes after a readonly agent
#
# Args:
#   workspace - Workspace directory
#   step_id   - Step ID (for logging)
_readonly_pop() {
    local workspace="$1"
    local step_id="$2"

    cd "$workspace" 2>/dev/null || return 0
    git stash pop 2>/dev/null || true
}
