#!/usr/bin/env bash
# validation-review.sh - Code review and validation agent
#
# Self-contained agent for reviewing completed work against PRD requirements.
# Uses single-shot execution pattern.
#
# Required paths: prd.md, workspace

AGENT_TYPE="validation-review"

# Source dependencies
source "$WIGGUM_HOME/lib/run-claude-once.sh"
source "$WIGGUM_HOME/lib/logger.sh"

# Required paths before agent can run
agent_required_paths() {
    echo "prd.md"
    echo "workspace"
}

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local max_turns="${3:-5}"

    local workspace="$worker_dir/workspace"
    local log_file="$worker_dir/logs/validation-review.log"

    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        VALIDATION_RESULT="UNKNOWN"
        return 1
    fi

    mkdir -p "$worker_dir/logs"

    # Clean up old validation files before re-running
    rm -f "$log_file" "$worker_dir/validation-result.txt" "$worker_dir/validation-review.md"

    log "Running validation review..."

    run_agent_once "$workspace" \
        "$(_get_system_prompt "$workspace")" \
        "$(_get_user_prompt)" \
        "$log_file" \
        "$max_turns"

    local agent_exit=$?

    # Parse result
    _extract_validation_result "$worker_dir"

    if [ $agent_exit -eq 0 ]; then
        log "Validation review completed with result: $VALIDATION_RESULT"
    else
        log_warn "Validation review had issues (exit: $agent_exit)"
    fi

    return $agent_exit
}

# System prompt
_get_system_prompt() {
    local workspace="$1"

    cat << EOF
VALIDATION REVIEWER ROLE:

You are a code reviewer and validation agent. Your job is to review completed work
and verify it meets the requirements specified in the PRD.

WORKSPACE: $workspace

You have READ-ONLY intent - focus on reviewing and validating, not making changes.
If you find issues, document them clearly but do not attempt fixes.
EOF
}

# User prompt
_get_user_prompt() {
    cat << 'EOF'
VALIDATION AND REVIEW TASK:

Review the completed work in this workspace against the requirements in @../prd.md.

REVIEW CHECKLIST:

1. **Requirements Verification**
   - Read the PRD and identify all requirements
   - For each completed task, verify the implementation meets the stated requirements
   - Check for any missed requirements or partial implementations

2. **Code Quality Review**
   - Check for obvious bugs, errors, or anti-patterns
   - Verify error handling is appropriate
   - Look for potential security issues (injection, XSS, hardcoded secrets, etc.)
   - Check for proper input validation at boundaries

3. **Implementation Consistency**
   - Verify code follows existing project patterns and conventions
   - Check naming conventions are consistent
   - Verify file organization matches project structure

4. **Testing Coverage**
   - Identify what testing was performed (documented in PRD or summaries)
   - Note any gaps in test coverage
   - Check if edge cases were considered

DECISION CRITERIA:

- PASS: All requirements met, no critical issues, code is production-ready
- FAIL: Missing requirements, critical bugs, security vulnerabilities, or broken functionality

OUTPUT FORMAT:

You MUST provide your response in this EXACT structure with both tags:

<review>

## Requirements Check

| Requirement | Status | Notes |
|-------------|--------|-------|
| [requirement] | [PASS/FAIL] | [brief note] |

## Issues Found

### Critical (blocks release)
- [issue description and location]

### Warnings (should fix)
- [issue description and location]

### Suggestions (optional)
- [suggestion]

## Security Review

[Any security concerns found, or confirmation that common issues were checked]

## Summary

[Brief overall assessment]

</review>

<result>PASS</result>

OR

<result>FAIL</result>

CRITICAL: The <result> tag MUST contain exactly one word: either PASS or FAIL. No other text.
This tag is parsed programmatically to determine if the work can proceed to commit/PR creation.
EOF
}

# Extract validation result from log file
_extract_validation_result() {
    local worker_dir="$1"
    local log_file="$worker_dir/logs/validation-review.log"

    VALIDATION_RESULT="UNKNOWN"

    if [ -f "$log_file" ]; then
        # Extract review content between <review> tags
        if grep -q '<review>' "$log_file"; then
            sed -n '/<review>/,/<\/review>/p' "$log_file" | sed '1d;$d' > "$worker_dir/validation-review.md"
            log "Validation review saved to validation-review.md"
        fi

        # Extract result tag (PASS or FAIL)
        VALIDATION_RESULT=$(grep -oP '(?<=<result>)(PASS|FAIL)(?=</result>)' "$log_file" | head -1)
        if [ -z "$VALIDATION_RESULT" ]; then
            VALIDATION_RESULT="UNKNOWN"
        fi
    fi

    # Store result for other scripts to read
    echo "$VALIDATION_RESULT" > "$worker_dir/validation-result.txt"
}

# Check validation result from a worker directory (utility for callers)
# Returns: 0 if PASS, 1 if FAIL or UNKNOWN
check_validation_result() {
    local worker_dir="$1"
    local result_file="$worker_dir/validation-result.txt"

    if [ ! -f "$result_file" ]; then
        return 1
    fi

    local result
    result=$(cat "$result_file")

    if [ "$result" = "PASS" ]; then
        return 0
    else
        return 1
    fi
}
