| name | description |
|------|-------------|
| intent-distill | Analyze a codebase and extract architectural patterns into Intent DSL specifications using structural extraction, behavioral summarization, and tool-validated refinement. |

# Intent Distill

## Purpose

Analyze a codebase and distill its architectural patterns into machine-readable Intent DSL specifications using `distilled pattern`, `distilled constraint`, and `rationale` constructs. The skill follows a three-phase methodology: structural extraction, behavioral summarization, and tool-validated refinement via `intent lint`.

**Output**: A `distilled.intent` file containing high-confidence patterns, constraints, and rationale extracted from the codebase.

## Input

**Optional**: A directory path to analyze (e.g., `src/`, `lib/pipeline/`). Defaults to the project root.

## When This Skill is Invoked

**Manual invocation:**
- `/intent-distill` - Distill the entire project
- `/intent-distill lib/pipeline/` - Distill patterns from a specific module
- `/intent-distill src/auth/` - Focus on a subsystem

**Use cases:**
- Documenting undocumented architectural patterns
- Onboarding to a new codebase by extracting its implicit rules
- Creating machine-readable specifications from existing code
- Validating that code follows consistent patterns
- Before major refactors, to capture current invariants

## Critical Rules

1. **READ-ONLY exploration** - Do NOT modify any source code. The only file you write is `distilled.intent`.
2. **Evidence-based only** - Every pattern and constraint must cite specific source files and locations. Never invent patterns not found in code.
3. **Confidence threshold** - Do not emit patterns with confidence < 0.5. Prefer fewer high-confidence patterns over many low-confidence ones.
4. **Validate with `intent lint`** - Always run `intent lint` on the output and fix errors before finishing.
5. **Use actual commit hash** - Run `git rev-parse HEAD` for the `commit` field; never use placeholder hashes.

## Core Workflow

### Phase 0: Toolchain Setup

**Ensure the `intent` CLI is available.**

1. Check if `intent` is on PATH: run `command -v intent`
2. If NOT found, install it:
   ```bash
   cargo binstall intent --no-confirm
   ```
3. If `cargo binstall` is not available, try:
   ```bash
   cargo install intent
   ```
4. Verify installation: `intent --version`
5. If installation fails entirely, warn the user and continue — the skill can produce a spec without lint validation, but the output will be lower confidence.

---

### Phase 1: Structural Extraction

**Goal:** Understand the codebase architecture before reading implementation details.

**Tasks:**
1. **Directory structure** - List top-level directories and key files
2. **Entry points** - Identify main entry points (`main.*`, `index.*`, `bin/*`, `cmd/*`, etc.)
3. **Dependencies** - Check for dependency manifests (`Cargo.toml`, `package.json`, `go.mod`, `pyproject.toml`, etc.)
4. **Module boundaries** - Identify major modules/packages and their responsibilities
5. **Component relationships** - Note which modules depend on which (imports, includes, references)

**Exploration tools (READ-ONLY):**
- **Glob**: Find files by pattern
- **Grep**: Search for imports, function definitions, type definitions
- **Read**: Examine specific files
- **Bash** (read-only): `ls`, `git log`, `git rev-parse HEAD`

**Output:** Mental model of the codebase architecture. Do NOT write `distilled.intent` yet.

**Ask scope question if target is large:**

```yaml
questions:
  - question: The codebase has N top-level modules. Should I distill all of them or focus on specific areas?
    header: Scope
    multiSelect: false
    options:
      - label: All modules (Recommended)
        description: Comprehensive extraction across the entire codebase
      - label: Core modules only
        description: Focus on the primary business logic, skip tests/docs/config
      - label: Let me choose
        description: I'll specify which modules to include
```

---

### Phase 2: Behavioral Extraction

**Goal:** Read implementation code and identify recurring patterns and structural constraints.

**For each significant component identified in Phase 1:**

1. **Read implementation code** - Focus on core logic, not boilerplate
2. **Extract behavioral patterns** - Look for:
   - State machines (states, transitions, events, guards, effects)
   - Retry logic (backoff, max attempts, error classification)
   - Lifecycle management (init/start/stop/cleanup)
   - Error handling patterns (error types, propagation, recovery)
   - Resource management (acquire/release, pooling)
   - Event-driven flows (publish/subscribe, callbacks, hooks, channels)
   - Pipeline/chain patterns (sequential processing stages)
   - Guard/precondition patterns (validation before action)
   - Parallel composition (fork/join, concurrent workflows)
   - Timing constraints (timeouts, deadlines, backoff durations)
3. **Extract structural constraints** - Look for:
   - Layering rules (which modules avoid depending on which)
   - Interface contracts (required methods, function signatures)
   - Naming conventions enforced structurally
   - Module containment rules (what lives where)
   - Dependency direction rules (no circular deps, unidirectional flow)
   - Transitive dependency rules (indirect dependency chains)
4. **Capture design decisions** - Look for:
   - Documented rationale in comments, ADRs, or README files
   - Rejected alternatives evident from code history or comments
   - Traceability from decisions to specific code locations

**Pattern detection heuristic:** If you see the same structure in 3+ locations, it is likely a pattern worth distilling. If 1-2 locations, note it but assign lower confidence.

**Output:** List of candidate patterns and constraints with source locations and preliminary confidence scores.

---

### Phase 3: Write Spec

**Goal:** Create the `distilled.intent` file with all extracted patterns and constraints.

**Write to `distilled.intent`** in the target directory (or project root if no target specified).

**For each pattern, use the `distilled pattern` construct:**
```intent
distilled pattern <Name> {
    source: "<glob>"
    commit: "<hash>"
    extracted: "<ISO-date>"
    confidence: <0.0-1.0>

    observation {
        "<human-readable description of what was observed>"
    }

    parameters {
        <name>: <Type> { default: <value> }
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

        property <name> {
            <temporal_expression>     // e.g., always(P => eventually(Q))
        }
    }

    applies_to { <scope_glob> }
}
```

**For each constraint, use the `distilled constraint` construct:**
```intent
distilled constraint <Name> {
    source: "<glob>"
    commit: "<hash>"
    confidence: <0.0-1.0>

    observation {
        "<human-readable description of what was observed>"
    }

    constraint {
        <predicate_expression>
    }
}
```

**For observed design decisions, use `rationale`:**
```intent
rationale <Name> {
    discovered: "<date>"
    source: "<origin>"

    observation { "<what was observed>" }
    decided because { "<reason>" }
    rejected { <alternative>: "<why rejected>" }
    traces_to { file: "<path>", commit: "<hash>" }
}
```

**Writing guidelines:**
- Include only patterns with confidence >= 0.5
- Use `git rev-parse HEAD` for the commit hash
- Use today's date for the `extracted` field
- Each pattern/constraint needs a clear `observation` explaining what was found
- Prefer descriptive PascalCase names (e.g., `RetryWithBackoff`, `ObservedLayering`)
- Not every pattern needs a full `behavior` block — simple patterns can omit it
- Not every pattern needs `parameters` — only include when the pattern is parameterized in the codebase
- Use `variables` in behavior blocks to declare state tracked across transitions (prefer explicit types)
- Use `property` blocks for temporal invariants the pattern should satisfy (e.g., `always(P => eventually(Q))`)
- Use `rationale` when you observe a design decision that isn't purely a pattern or constraint
- Constraint predicates include `depends`, `depends_transitively`, `references`, `implements`, `contains`
- Use `allow { ... }` blocks on constraints when exceptions exist (document the exception, reason, and tracking)
- Define `predicate` macros for reusable constraint logic (e.g., `predicate isolated(a, b) { !a.depends(b) && !a.references(b) }`)

For full DSL reference, see references/intent-dsl-reference.md.

---

### Phase 4: Validate and Refine

**Goal:** Run `intent lint` and iterate until the spec passes validation.

1. Run `intent lint distilled.intent` (adjust path to where you wrote it)
2. If lint errors are found:
   - Read the error messages carefully
   - Fix syntax errors, missing fields, invalid constructs
   - Re-run lint
   - Repeat until clean
3. If lint passes, review the spec one final time:
   - Are confidence scores calibrated? (see references/confidence-calibration.md)
   - Are observations accurate and specific?
   - Are source globs correct?

**If `intent` CLI is not available** (installation failed in Phase 0):
- Manually review the spec for syntactic correctness against the DSL reference
- Check that all required fields are present
- Warn the user that the output has not been machine-validated

**Iterate up to 3 times** on lint failures. If the spec still doesn't pass after 3 attempts, present the remaining errors to the user and ask how to proceed.

---

### Phase 5: Summary

**Present results to the user:**
- Number of patterns extracted (with confidence distribution)
- Number of constraints extracted
- Number of rationale blocks (if any)
- Key findings — the most interesting or surprising patterns
- Lint status (pass/fail/not-validated)
- Output file location
- Suggested next steps (review specific patterns, run on other modules, use patterns for enforcement)

## Key Principles

1. **Evidence over invention** - Only distill patterns actually found in code. Every pattern cites source locations.
2. **Confidence calibration** - Score patterns honestly based on frequency and consistency. See references/confidence-calibration.md.
3. **Fewer is better** - 5 high-confidence patterns are more valuable than 20 low-confidence ones.
4. **Validate with tooling** - Always lint the output. Machine validation catches mistakes humans miss.
5. **Read-only** - Never modify source code. The only output is `distilled.intent`.
6. **Structural before behavioral** - Understand the architecture before diving into implementation details.

## Progressive Disclosure

This SKILL.md contains the core workflow. For detailed guidance:
- **Intent DSL syntax**: references/intent-dsl-reference.md
- **Confidence scoring**: references/confidence-calibration.md
