#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: resume-decide
# AGENT_DESCRIPTION: Analyzes previous worker conversation logs and worker.log
#   to decide which step to resume from (or ABORT). Produces resume instructions
#   for the resumed worker with context about what was accomplished and what
#   needs to happen next.
# REQUIRED_PATHS:
#   - conversations : Directory with converted conversation markdown files
#   - worker.log    : Phase-level status log from previous run
# OUTPUT_FILES:
#   - resume-step.txt         : Contains the step name to resume from (or ABORT)
#   - resume-instructions.md  : Context and guidance for the resumed worker
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "resume-decide" "Analyzes logs to decide resume step"

# Required paths before agent can run
agent_required_paths() {
    echo "conversations"
    echo "worker.log"
}

# Output files that must exist (non-empty) after agent completes
agent_output_files() {
    echo "resume-step.txt"
    echo "resume-instructions.md"
}

# Source dependencies
agent_source_core
agent_source_once

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # $3 is max_iterations (unused — this agent runs once)
    local max_turns="${4:-25}"

    local conversations_dir="$worker_dir/conversations"
    local worker_log="$worker_dir/worker.log"

    log "Resume-decide agent analyzing previous run..."

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Build a lightweight user prompt with file paths for the agent to explore
    local user_prompt
    user_prompt=$(_build_user_prompt "$worker_dir")

    # Run Claude with tool access so it can read the files itself
    local workspace="$worker_dir"
    [ -d "$worker_dir/workspace" ] && workspace="$worker_dir/workspace"

    run_agent_once "$workspace" \
        "$(_get_system_prompt "$worker_dir")" \
        "$user_prompt" \
        "$worker_dir/logs/resume-decide.log" \
        "$max_turns"

    local agent_exit=$?

    # Extract decision from the log output
    _extract_decision "$worker_dir"

    if [ $agent_exit -ne 0 ]; then
        log_warn "Resume-decide agent exited with code $agent_exit"
    fi

    # Verify outputs exist
    if [ ! -f "$worker_dir/resume-step.txt" ] || [ ! -s "$worker_dir/resume-step.txt" ]; then
        log_error "resume-decide failed to produce resume-step.txt"
        echo "ABORT" > "$worker_dir/resume-step.txt"
        echo "Resume-decide agent failed to produce a decision." > "$worker_dir/resume-instructions.md"
        return 1
    fi

    local step
    step=$(cat "$worker_dir/resume-step.txt")
    log "Resume decision: $step"

    return 0
}

# System prompt for the resume-decide agent
_get_system_prompt() {
    local worker_dir="$1"

    cat << EOF
RESUME DECISION AGENT

You are analyzing a previously interrupted worker run to decide where to resume from.
You have access to tools (Read, Glob, Grep) to explore the worker directory and understand what happened.

## Worker Directory

All files are located under: $worker_dir

Key paths to explore:
- $worker_dir/worker.log — Phase-level status log (READ THIS FIRST)
- $worker_dir/prd.md — The task requirements (check completion status)
- $worker_dir/conversations/ — Converted conversation logs from the previous run
  - iteration-*.md files show the main work loop conversations
  - audit-*.md, test-*.md, etc. show sub-agent conversations

## Available Steps (in order)

1. \`execution\` - The main work loop (ralph loop iterations). Resume here means restarting the ENTIRE work loop from scratch. You cannot resume between iterations.
2. \`audit\` - Security audit phase
3. \`test\` - Test coverage phase
4. \`docs\` - Documentation writer phase
5. \`validation\` - Validation review phase
6. \`finalization\` - Commit/PR creation phase

## Decision Rules

- If the execution phase (ralph loop) was interrupted mid-iteration, you MUST resume from \`execution\` (you cannot resume between iterations)
- If execution completed successfully (all PRD tasks marked [x]) but a later phase failed or wasn't reached, resume from that phase
- If the worker failed due to a fundamental issue (bad PRD, impossible task, repeated failures), output ABORT
- If all phases completed successfully, output ABORT (nothing to resume)
- Prefer resuming from the earliest incomplete phase to ensure correctness

## How to Identify Phase Completion

- **execution complete**: worker.log shows "Task completed successfully" or PRD has all tasks marked [x]
- **audit complete**: worker.log shows "Security audit" result (PASS/FIX/STOP)
- **test complete**: worker.log shows "Test coverage result"
- **docs complete**: worker.log shows "Documentation writer result"
- **validation complete**: worker.log shows "validation review" ran
- **finalization complete**: worker.log shows "PR created" or "Commit created"

## Output Format

You MUST output your decision in these exact XML tags.
The step value MUST be exactly one of these literal strings:
  execution
  audit
  test
  docs
  validation
  finalization
  ABORT

Example: <step>audit</step>

<instructions>
Detailed instructions for the resumed worker. Include:
- What was accomplished before the interruption
- What specifically needs to happen in the resumed phase
- Any important context from the previous run (patterns used, decisions made, files modified)
- Warnings about issues encountered in the previous run
</instructions>

## Important

- Start by reading worker.log to understand the phase-level status
- Then check prd.md for task completion status
- Only read conversation files if you need more detail about what happened
- Be thorough in your analysis but decisive in your output
- The instructions will be injected into the resumed worker's prompt, so write them as guidance for a developer
- If the workspace has code changes from completed execution, those changes are preserved
EOF
}

# Build user prompt — lightweight, just tells the agent to explore
_build_user_prompt() {
    local worker_dir="$1"

    # List available conversation files for the agent's awareness
    local conv_files=""
    if [ -d "$worker_dir/conversations" ]; then
        conv_files=$(ls "$worker_dir/conversations/"*.md 2>/dev/null | sort || true)
    fi

    cat << EOF
Analyze the previous worker run and decide which step to resume from.

Start by reading these files:
1. $worker_dir/worker.log — to understand which phases ran and their results
2. $worker_dir/prd.md — to check task completion status

Available conversation logs (read as needed for detail):
$conv_files

Based on your analysis, determine:
1. Which phases completed successfully?
2. Where was the worker interrupted?
3. What step should we resume from (or should we ABORT)?

Output your decision using the <step> and <instructions> XML tags.
EOF
}

# Extract decision from resume-decide log output
_extract_decision() {
    local worker_dir="$1"
    local log_file="$worker_dir/logs/resume-decide.log"

    if [ ! -f "$log_file" ]; then
        log_error "No resume-decide log file found at $log_file"
        echo "ABORT" > "$worker_dir/resume-step.txt"
        echo "No decision log produced." > "$worker_dir/resume-instructions.md"
        return 1
    fi

    local log_size
    log_size=$(wc -c < "$log_file" 2>/dev/null || echo 0)
    log "Resume-decide log: $log_file ($log_size bytes)"

    # Extract assistant text from stream-JSON
    local full_text
    full_text=$(grep '"type":"assistant"' "$log_file" | \
        jq -r 'select(.message.content[]? | .type == "text") | .message.content[] | select(.type == "text") | .text' 2>/dev/null || true)

    if [ -z "$full_text" ]; then
        log_error "No assistant text found in resume-decide log"
        # Log first few lines of the file for debugging
        log_error "Log file head: $(head -5 "$log_file" 2>/dev/null | tr '\n' ' ')"
        echo "ABORT" > "$worker_dir/resume-step.txt"
        echo "Failed to extract decision from agent output." > "$worker_dir/resume-instructions.md"
        return 1
    fi

    # Log the agent's response for debugging
    local text_preview
    text_preview=$(echo "$full_text" | head -20)
    log "Resume-decide agent response (first 20 lines):"
    log "$text_preview"

    # Extract step from <step>...</step> tags
    local step
    step=$(echo "$full_text" | sed -n 's/.*<step>\([^<]*\)<\/step>.*/\1/p' | head -1 | tr -d '[:space:]')

    if [ -z "$step" ]; then
        log_error "No <step> tag found in resume-decide output"
        log_error "Full agent response: $full_text"
        echo "ABORT" > "$worker_dir/resume-step.txt"
        echo "Agent did not produce a step decision." > "$worker_dir/resume-instructions.md"
        return 1
    fi

    # Validate step name
    case "$step" in
        execution|audit|test|docs|validation|finalization|ABORT)
            echo "$step" > "$worker_dir/resume-step.txt"
            ;;
        *)
            log_error "Invalid step name from resume-decide: $step"
            echo "ABORT" > "$worker_dir/resume-step.txt"
            step="ABORT"
            ;;
    esac

    # Extract instructions from <instructions>...</instructions> tags
    local instructions
    instructions=$(echo "$full_text" | sed -n '/<instructions>/,/<\/instructions>/p' | sed '1d;$d')

    if [ -z "$instructions" ]; then
        instructions="Resuming from step: $step. No detailed instructions available."
    fi

    echo "$instructions" > "$worker_dir/resume-instructions.md"

    log "Extracted decision: step=$step"
    return 0
}
