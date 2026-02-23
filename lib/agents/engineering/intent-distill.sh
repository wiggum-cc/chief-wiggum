#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: intent-distill
# AGENT_DESCRIPTION: Distills codebase patterns into Intent DSL specifications
#   using a three-phase methodology: structural extraction, behavioral
#   summarization, and tool-validated refinement via `intent lint`.
# REQUIRED_PATHS:
#   - workspace : Directory containing the code to analyze
# OUTPUT_FILES:
#   - distilled.intent             : Generated Intent DSL specification
#   - intent-distill-result.json   : Contains PASS, FIX, or FAIL
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "engineering.intent-distill" "Distills codebase patterns into Intent DSL specifications"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Valid result values for this agent
agent_valid_results() {
    echo "PASS|FAIL|FIX"
}

# Source dependencies using base library helpers
agent_source_core
agent_source_ralph

# Cache for intent CLI availability check
_INTENT_AVAILABLE=""
_INTENT_AVAILABLE_BIN=""

# Check if intent CLI is available
#
# Returns: 0 if available, 1 if not
_check_intent_cli() {
    local bin="${WIGGUM_INTENT_BIN:-intent}"
    # Invalidate cache if binary path changed
    if [ -n "$_INTENT_AVAILABLE" ] && [ "$_INTENT_AVAILABLE_BIN" = "$bin" ]; then
        [ "$_INTENT_AVAILABLE" = "1" ]
        return
    fi
    if command -v "$bin" >/dev/null 2>&1; then
        _INTENT_AVAILABLE="1"
        _INTENT_AVAILABLE_BIN="$bin"
        return 0
    else
        _INTENT_AVAILABLE="0"
        _INTENT_AVAILABLE_BIN="$bin"
        return 1
    fi
}

# Run intent lint on a spec file
#
# Args:
#   spec_file - Path to the .intent file
#
# Returns: 0 if lint passes, 1 if errors found
# Stdout: lint output (errors/warnings)
_run_intent_lint() {
    local spec_file="$1"
    local bin="${WIGGUM_INTENT_BIN:-intent}"
    "$bin" lint "$spec_file" 2>&1
}

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # Use config values (set by load_agent_config in agent-registry, with env var override)
    local max_iterations="${WIGGUM_INTENT_DISTILL_MAX_ITERATIONS:-${AGENT_CONFIG_MAX_ITERATIONS:-8}}"
    local max_turns="${WIGGUM_INTENT_DISTILL_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-80}}"

    local workspace="$worker_dir/workspace"
    local spec_file="$worker_dir/reports/distilled.intent"

    # Record start time and log agent start
    local start_time
    start_time=$(epoch_now)
    agent_log_start "$worker_dir" "$(basename "$worker_dir")"

    # Verify workspace exists
    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        agent_log_complete "$worker_dir" 1 "$start_time"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Workspace not found"]'
        return 1
    fi

    # Check intent CLI availability
    if _check_intent_cli; then
        log "Intent CLI found: $_INTENT_BIN"
    else
        log_warn "Intent CLI not found at '$_INTENT_BIN' - lint validation will be skipped"
    fi

    # Set up callback context using base library
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"
    _DISTILL_SPEC_FILE="$spec_file"
    _DISTILL_WORKSPACE="$workspace"

    log "Starting intent distill loop (max $max_iterations iterations, $max_turns turns/session)"

    # Use step ID from pipeline for session prefix
    local session_prefix="${WIGGUM_STEP_ID:-distill}"

    # Run the distill loop
    run_ralph_loop \
        "$workspace" \
        "$(_get_system_prompt "$workspace")" \
        "_distill_user_prompt" \
        "_distill_completion_check" \
        "$max_iterations" \
        "$max_turns" \
        "$worker_dir" \
        "$session_prefix"

    local loop_result=$?

    # Determine gate result
    local gate_result="FAIL"
    if [ -f "$spec_file" ] && [ -s "$spec_file" ]; then
        if _check_intent_cli; then
            local lint_output=""
            local lint_exit=0
            lint_output=$(_run_intent_lint "$spec_file") || lint_exit=$?
            if [ "$lint_exit" -eq 0 ]; then
                gate_result="PASS"
            else
                gate_result="FIX"
                log_warn "Intent lint failed on output spec: $lint_output"
            fi
        else
            # Graceful fallback: check for distilled keyword
            if grep -q 'distilled' "$spec_file" 2>/dev/null; then
                gate_result="PASS"
            else
                gate_result="FIX"
            fi
        fi
    fi

    # Log completion and write structured result
    agent_log_complete "$worker_dir" "$loop_result" "$start_time"

    local lint_passed="false"
    [ "$gate_result" = "PASS" ] && lint_passed="true"

    local outputs_json
    outputs_json=$(printf '{"lint_passed":%s,"intent_cli_available":%s,"spec_file":"%s"}' \
        "$lint_passed" \
        "$( [ "$_INTENT_AVAILABLE" = "1" ] && echo "true" || echo "false" )" \
        "$spec_file")

    agent_write_result "$worker_dir" "$gate_result" "$outputs_json"

    return $loop_result
}

# System prompt
_get_system_prompt() {
    local workspace="$1"

    cat << 'SYSPROMPT_EOF'
CODE PATTERN DISTILLER:

You analyze codebases and extract architectural patterns into Intent DSL specifications
using `distilled pattern`, `distilled constraint`, and `rationale` constructs.

## Three-Phase Methodology

1. **Structural Extraction** (iteration 0): Scan directory structure, read entry points,
   identify components, dependencies, and module boundaries. Write a structural analysis.

2. **Behavioral Summarization** (iteration 1): For each significant component, read
   implementation code. Extract state machines, retry patterns, lifecycle flows, layering
   rules, design decisions. Write first draft of `reports/distilled.intent`.

3. **Tool-Validated Refinement** (iteration 2+): Run `intent lint reports/distilled.intent`,
   fix any errors, add missing patterns, refine confidence scores. Iterate until lint passes.

## Intent DSL Reference (Subset)

### Distilled Pattern (captures behavioral patterns from code)

```intent
distilled pattern <Name> {
    source: "<glob>"           // where the pattern was found (required)
    commit: "<hash>"           // commit at extraction time (required)
    extracted: "<date>"        // ISO date of extraction
    confidence: <0.0-1.0>     // extraction certainty

    observation {
        "<human-readable description of what was observed>"
    }

    parameters {
        <name>: <Type> { default: <value> }
        // Types: Int, Nat, Float, String, Bool, Duration, Set(T), Seq(T)
    }

    behavior {
        variables {
            <name>: <Type> = <initial_value>
        }

        states {
            <name> { initial: true }
            <name>
            <name> { terminal: true }
        }

        transitions {
            <from> -> <to> on <event>
            <from> -> <to> on <event> where { <condition> }
            <from> -> <to> on <event> effect { <action> }
            <from> -> <to> on <event> after { <duration> }
            * -> <to> on <event>                           // wildcard source
            [s1, s2] -> <to> on <event>                    // multi-source
            <from> -> fork { s1, s2 } on <event>           // parallel fork
            join { s1, s2 } -> <to> on <event>             // parallel join
        }

        // Effects execute simultaneously (not sequentially):
        // variable = expr, emit Event(args), send Channel.Msg(args)

        composes [BehaviorA, BehaviorB]    // composition

        property <name> {
            <temporal_expression>
        }

        fairness {
            weak(<from> -> <to>)
            strong(<from> -> <to>)
        }
    }

    applies_to { <scope_glob> }  // suggested enforcement scope
}
```

### Distilled Constraint (captures structural rules from code)

```intent
distilled constraint <Name> {
    source: "<glob>"
    commit: "<hash>"
    confidence: <0.0-1.0>

    observation {
        "<human-readable description of what was observed>"
    }

    constraint {
        // Predicates:
        //   A.depends(B)              - A imports/uses B (direct)
        //   A.depends_transitively(B) - A depends on B through a chain
        //   A.references(B)           - A mentions type B (no import needed)
        //   A.implements(T)           - A implements trait/interface T
        //   A.contains(B)             - B is nested within A
        //
        // Operators: ! (negation), && (and), || (or), => (implies), <=> (iff)
        // Quantifiers: forall x in S: P(x), exists x in S: P(x)
        // Scopes: [A, B], all, { x | x matches *Glob }, A | B, A & B, A \ B
        // Comparison: forall x in S: check x.field < value
        <predicate_expression>

        // Optional suppression for known exceptions:
        // !A.depends(B) allow {
        //     exception: [LegacyA]
        //     reason: "Migration in progress"
        //     tracking: "TASK-123"
        // }
    }
}
```

### User-Defined Predicates

```intent
predicate isolated(source, target) {
    !source.depends(target) && !source.references(target)
}
```

### Rationale (captures observed design decisions)

```intent
rationale <Name> {
    discovered: "<date>"
    source: "<origin>"

    observation { "<what was observed>" }
    decided because { "<reason>" }
    rejected { <alternative>: "<why rejected>" }
    revisit when { "<condition>" }
    traces_to { file: "<path>", commit: "<hash>" }
}
```

### Behavior States and Transitions

```intent
behavior <Name> {
    variables {
        retries: Nat = 0
        pending: Set(Id) = {}
    }

    states {
        pending   { initial: true }
        active
        completed { terminal: true }
        failed    { terminal: true }
    }

    transitions {
        pending -> active      on start
        active -> completed    on finish     where { all_checks_pass }
        active -> failed       on error
        active -> active       on retry      where { retries < max_retries }
                                             effect { retries = retries + 1 }
        * -> failed            on fatal_error
    }

    property eventual_completion {
        always(pending => eventually(completed | failed))
    }
}
```

### Temporal Operators

- `always(P)` — P holds in every state (safety)
- `eventually(P)` — P holds in some future state (liveness)
- `next(P)` — P holds in the next state
- `P until Q` — P holds until Q becomes true (strong)
- `P releases Q` — Q holds until P becomes true (weak)
- `P <=> Q` — biconditional
- `count(state)` — cardinality (distributed systems)

### Constraint Predicates

```intent
constraint <name> {
    !services.depends(storage_backends)
    services.references([AppError]) && !services.references([RawError])
    m.depends(cache) => m.depends(cache_invalidation)
    forall s in services: s.references([AppError])
    forall c in { x | x matches *Client }: storage.contains(c)
    a.depends(b) <=> b.implements(Interface)
}
```

### Non-Functional Constraints

```intent
constraint performance {
    p99(settle) < 100ms
    p95(validate) < 10ms
    throughput(system) > 10_000 / s
}
```

## Few-Shot Examples

### Example 1: Retry Pattern

```intent
distilled pattern RetryWithBackoff {
    source: "crates/client/src/*.rs"
    commit: "a1b2c3d"
    extracted: "2026-02-15"
    confidence: 0.85

    observation {
        "Exponential backoff pattern found in 5 client implementations."
    }

    parameters {
        max_attempts: Int { default: 3 }
        backoff_factor: Float { default: 2.0 }
    }

    behavior {
        variables {
            attempt: Nat = 0
        }

        states {
            idle       { initial: true }
            attempting
            waiting
            succeeded  { terminal: true }
            failed     { terminal: true }
        }

        transitions {
            idle -> attempting       on request
            attempting -> succeeded  on success
            attempting -> waiting    on transient_error  where { attempt < max_attempts }
                                                        effect { attempt = attempt + 1 }
            attempting -> failed     on transient_error  where { attempt >= max_attempts }
            attempting -> failed     on permanent_error
            waiting -> attempting    on backoff_elapsed
        }

        property eventual_resolution {
            always(attempting => eventually(succeeded | failed))
        }
    }

    applies_to { *Client.call }
}
```

### Example 2: Layering Constraint

```intent
distilled constraint ObservedLayering {
    source: "src/**/*.rs"
    commit: "b2c3d4e"
    confidence: 0.92

    observation {
        "All service modules avoid direct storage dependencies."
    }

    constraint {
        !services.depends(storage_backends)
    }
}
```

### Example 3: Design Decision

```intent
rationale EventDrivenLifecycle {
    discovered: "2026-02-23"
    source: "Code analysis"

    observation {
        "State machine loaded from JSON config rather than hardcoded transitions."
    }

    decided because {
        "Decouples state machine definition from engine implementation."
    }

    rejected {
        hardcoded_states: "Requires code changes for every new state."
    }

    traces_to {
        file: "config/worker-lifecycle.json"
        commit: "d4e5f6a"
    }
}
```

## Confidence Calibration

- **0.9+**: Pattern found in 5+ locations with consistent structure
- **0.7-0.9**: Pattern found in 3+ locations with minor variations
- **0.5-0.7**: Pattern found in 1-2 locations
- **< 0.5**: Do not emit (insufficient evidence)

## Soundness Note

Distilled artifacts are advisory by default. The `confidence` field indicates extraction
certainty based on pattern frequency and consistency across the codebase.

## Output Rules

- Write the distilled spec to `reports/distilled.intent` (relative to worker dir, i.e., `../reports/distilled.intent` from workspace)
- Include only patterns with confidence >= 0.5
- Prefer fewer high-confidence patterns over many low-confidence ones
- Each pattern/constraint needs a clear `observation` explaining what was found
- Use `git rev-parse HEAD` for the commit hash
- Declare variables explicitly with types in behavior blocks
- Use temporal properties to express invariants patterns should satisfy
- Use `rationale` for design decisions that aren't purely patterns or constraints
SYSPROMPT_EOF

    echo ""
    echo "WORKSPACE: $workspace"
    echo ""
    agent_get_memory_context
}

# User prompt callback (unified 4-arg signature)
_distill_user_prompt() {
    local iteration="$1"
    local output_dir="$2"
    # shellcheck disable=SC2034  # supervisor args unused but part of unified callback signature
    local _supervisor_dir="${3:-}"
    local _supervisor_feedback="${4:-}"

    if [ "$iteration" -eq 0 ]; then
        # Phase 1: Structural Extraction
        cat << 'EOF'
PHASE 1 - STRUCTURAL EXTRACTION:

Scan the workspace to understand the codebase architecture.

## Tasks

1. **Directory structure**: List top-level directories and key files
2. **Entry points**: Identify main entry points (main.*, index.*, bin/*, etc.)
3. **Dependencies**: Check for dependency manifests (Cargo.toml, package.json, go.mod, etc.)
4. **Module boundaries**: Identify major modules/packages and their responsibilities
5. **Component relationships**: Note which modules depend on which

## Output

Write your structural analysis in a `<structural-analysis>` block. This analysis will
inform the behavioral extraction in the next phase.

Do NOT write the distilled.intent file yet - focus on understanding the codebase first.
EOF
    else
        # Phase 2+: Behavioral Extraction and Refinement
        cat << 'PHASE2_EOF'
PHASE 2+ - BEHAVIORAL EXTRACTION & REFINEMENT:

Based on your structural analysis, extract behavioral patterns and structural constraints.

## Tasks

1. **Read implementation code** for each major component identified in Phase 1
2. **Extract patterns**: Look for state machines, retry logic, lifecycle management,
   error handling patterns, resource management (acquire/release), event-driven flows
3. **Extract constraints**: Look for layering rules (which modules avoid depending on
   which), interface contracts, naming conventions enforced structurally
4. **Write spec**: Create/update `../reports/distilled.intent` with `distilled pattern`
   and `distilled constraint` constructs
5. **Validate**: Run `intent lint ../reports/distilled.intent` and fix any errors
PHASE2_EOF

        # Inject lint errors if available from previous iteration
        local spec_file="${_DISTILL_SPEC_FILE:-}"
        if [ -n "$spec_file" ] && [ -f "$spec_file" ] && _check_intent_cli; then
            local lint_output=""
            local lint_exit=0
            lint_output=$(_run_intent_lint "$spec_file") || lint_exit=$?
            if [ "$lint_exit" -ne 0 ]; then
                cat << LINT_EOF

## Lint Errors (from previous iteration)

The following errors were found by \`intent lint\`. Fix these:

\`\`\`
$lint_output
\`\`\`
LINT_EOF
            fi
        fi

        # Add continuation context from previous iterations
        local prev_iter=$((iteration - 1))
        local run_id="${RALPH_RUN_ID:-}"
        if [ -n "$run_id" ] && [ -f "$output_dir/summaries/$run_id/distill-$prev_iter-summary.txt" ]; then
            cat << CONTEXT_EOF

## Continuation Context (Iteration $iteration)

- Read @../summaries/$run_id/distill-$prev_iter-summary.txt for previous work context
- Do NOT repeat analysis already completed
- Focus on writing/refining the distilled.intent spec and passing lint
CONTEXT_EOF
        fi
    fi
}

# Completion check callback
_distill_completion_check() {
    local spec_file="${_DISTILL_SPEC_FILE:-}"

    # If spec file doesn't exist or is empty, not complete
    if [ ! -f "$spec_file" ] || [ ! -s "$spec_file" ]; then
        return 1
    fi

    # If intent CLI available, validate with lint
    if _check_intent_cli; then
        local lint_exit=0
        _run_intent_lint "$spec_file" >/dev/null 2>&1 || lint_exit=$?
        return $lint_exit
    fi

    # Fallback: check for distilled keyword presence
    if grep -q 'distilled' "$spec_file" 2>/dev/null; then
        return 0
    fi

    return 1
}
