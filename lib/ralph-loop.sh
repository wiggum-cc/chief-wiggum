#!/usr/bin/env bash
# Ralph Wiggum Loop - Self-prompting execution pattern with controlled context

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/task-parser.sh"
source "$SCRIPT_DIR/logger.sh"

ralph_loop() {
    local prd_file="$1"                    # Worker's PRD file (absolute path)
    local agent_file="$2"                  # Agent definition
    local workspace="$3"                   # Worker's git worktree
    local max_iterations="${4:-50}"
    local max_turns_per_session="${5:-20}" # Limit turns to control context window
    local iteration=0

    log "Ralph loop starting for $prd_file (max $max_turns_per_session turns per session)"

    # Change to workspace BEFORE the loop
    cd "$workspace" || exit 1

    # Convert PRD file to relative path from workspace
    local prd_relative="../prd.md"

    while [ $iteration -lt $max_iterations ]; do
        # Exit if all tasks complete
        if ! has_incomplete_tasks "$prd_file"; then
            log "Worker completed all tasks in $prd_file"
            break
        fi

        # Generate unique session ID for this iteration
        local session_id=$(uuidgen)

        local sys_prompt="Your working directory is $workspace. Do NOT directly or indirectly cd into, read, or modify files outside this directory."
        local user_prompt="Read @$prd_relative, find the next incomplete task (- [ ]), execute it completely within your working directory, then mark it as complete (- [x]) by editing the PRD file. If you are unable to complete the task, mark it as failed (- [*]) by editing the PRD file."

        log_debug "Iteration $iteration: Session $session_id (max $max_turns_per_session turns)"

        # Debug output
        {
            echo "=== ITERATION $iteration ==="
            echo "Session ID: $session_id"
            echo "Max turns: $max_turns_per_session"
            echo "PWD: $(pwd)"
            echo "=== WORK PHASE ==="
        } >> "../worker.log"

        # PHASE 1: Work session with turn limit
        # Use --dangerously-skip-permissions to allow PRD edits (hooks still enforce workspace boundaries)
        claude --verbose \
            --output-format stream-json \
            --plugin-dir "$WIGGUM_HOME/skills" \
            --append-system-prompt "$sys_prompt" \
            --session-id "$session_id" \
            --max-turns "$max_turns_per_session" \
            --dangerously-skip-permissions \
            -p "$user_prompt" >> "../worker.log" 2>&1

        local exit_code=$?

        # PHASE 2: If session hit turn limit (exit code 1), resume for summary
        if [ $exit_code -ne 0 ]; then
            log "Session $session_id hit turn limit, requesting summary"

            {
                echo "=== SUMMARY PHASE ==="
            } >> "../worker.log"

            local summary_prompt="Provide a concise summary (3-5 bullet points) of what you accomplished in this session. Include: what task you worked on, what you completed, and what remains. Format as markdown bullets."

            # Resume session to get summary (limit to 2 turns for summary only)
            local summary=$(claude --resume "$session_id" --max-turns 2 --dangerously-skip-permissions -p "$summary_prompt" 2>&1 | tee -a "../worker.log")

            # Append summary to PRD changelog section
            {
                echo ""
                echo "## Session $iteration Changelog ($(date -u +"%Y-%m-%d %H:%M:%S UTC"))"
                echo ""
                echo "$summary"
                echo ""
            } >> "$prd_file"

            log "Summary appended to PRD"
        fi

        iteration=$((iteration + 1))
        sleep 2  # Prevent tight loop
    done

    if [ $iteration -ge $max_iterations ]; then
        log_error "Worker reached max iterations ($max_iterations) without completing all tasks"
        return 1
    fi

    log "Worker finished after $iteration iterations"
    return 0
}
