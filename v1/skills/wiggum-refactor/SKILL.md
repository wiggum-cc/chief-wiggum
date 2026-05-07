| name | description |
|------|-------------|
| wiggum-refactor | Analyze accumulated code changes for spec compliance, pattern extraction, and simplification opportunities. |

# Wiggum Refactor

## Purpose

Perform post-hoc analysis of modules after multiple PRs to:
1. **Extract generalizable patterns** - Identify reusable patterns that should be added to spec documents
2. **Identify spec deviations** - Find code that deviates from specifications and suggest reshaping
3. **Simplify accumulated complexity** - Recommend module restructuring and cleanup

This skill addresses the natural accumulation of technical debt when code grows organically through many tasks without periodic review.

## Input

Module path or file glob pattern (e.g., `lib/pipeline/`, `src/auth/**/*.ts`).

## When This Skill is Invoked

**Manual invocation:**
- After multiple tasks (~5+) have touched the same module
- During periodic cleanup cycles
- When a module feels "messy" or hard to navigate
- Before major architectural changes

**Typical flow:**
1. `/wiggum-refactor lib/pipeline/` analyzes the module
2. User reviews recommendations
3. User selects which to add to kanban
4. `/kanban` or direct task creation formalizes selected recommendations
5. Workers implement the refactoring tasks

## Critical Rules

1. **Read before recommending** - Never suggest changes without reading actual code
2. **Reference specs explicitly** - Every deviation must cite specific spec section
3. **Preserve behavior** - Refactoring should not change functionality
4. **Ground in evidence** - Every recommendation needs file:line citations
5. **Respect existing patterns** - Don't impose new patterns, extract existing ones

## Core Workflow

### Phase 1: Scope and Context

**Get the module path:**
- User provides path or glob (e.g., `lib/pipeline/`, `src/auth/**/*.ts`)
- Validate the path exists

**Discover spec documents:**
- Glob for `docs/**/*.md` and `*.md` in project root
- Identify authoritative specs for this module

**Ask about refactoring priorities:**

```yaml
questions:
  - question: What is your primary refactoring goal?
    header: Goal
    options:
      - label: Spec compliance
        description: Ensure code matches specifications, reshape deviations
      - label: Pattern extraction
        description: Identify reusable patterns for spec generalization
      - label: Simplification
        description: Reduce complexity, improve maintainability
      - label: All of the above
        description: Comprehensive analysis
```

**When multiple spec documents found:**

```yaml
questions:
  - question: Which spec documents are authoritative for this module?
    header: Specs
    multiSelect: true
    options:
      - label: docs/ARCHITECTURE.md
        description: System architecture and component design
      - label: docs/PROTOCOL.md
        description: Inter-component communication contracts
      - label: README.md
        description: Project-level conventions and patterns
      - label: CLAUDE.md
        description: Development guidelines and constraints
```

### Phase 2: Deep Analysis

**Analyze current state only** (no git archaeology).

**2.1 Pattern Mining:**
- Find repeated code structures across files in the module
- Identify ad-hoc conventions that emerged organically
- Look for similar function signatures, error handling patterns, data flows
- Note any TODO/FIXME comments indicating known issues

**2.2 Spec Comparison:**
- Cross-reference implementation against discovered spec documents
- Identify features in code but not in spec (candidates for generalization)
- Find implementations that deviate from spec (candidates for reshaping)
- Note naming inconsistencies with spec terminology

**2.3 Complexity Assessment:**
- Count files, functions, lines in module
- Identify coupling between components
- Find overly complex functions (too many responsibilities)
- Look for premature abstractions or unnecessary indirection

**Ask when patterns are unclear:**

```yaml
questions:
  - question: Found repeated pattern across N files. Should this be added to spec?
    header: Pattern
    options:
      - label: Add to spec
        description: "Pattern: <description>. Files: <list>"
      - label: Keep as-is
        description: This is context-specific, doesn't need formalization
      - label: Investigate more
        description: Show me the actual code before deciding
```

**Ask when deviations are found:**

```yaml
questions:
  - question: Code deviates from spec. How should we handle it?
    header: Deviation
    options:
      - label: Reshape code
        description: "Spec says X, code does Y. Change code to match spec"
      - label: Update spec
        description: Code behavior is correct, spec is outdated
      - label: Extend spec
        description: Add new option/variant to spec to cover this case
      - label: Flag as tech debt
        description: Track for future cleanup, not urgent
```

**Ask about simplification aggressiveness:**

```yaml
questions:
  - question: How aggressive should simplification recommendations be?
    header: Simplify
    options:
      - label: Conservative
        description: Only obvious wins, minimal risk
      - label: Moderate
        description: Suggest consolidation where patterns repeat
      - label: Aggressive
        description: Recommend restructuring even if requires significant changes
```

**Ask about undocumented features:**

```yaml
questions:
  - question: Found feature not documented in any spec. What should we do?
    header: Undocumented
    options:
      - label: Document it
        description: "Feature: X in file Y. Add to spec as new capability"
      - label: Flag for removal
        description: May be scope creep or dead code, investigate
      - label: Ask original author
        description: Needs context on why this was added
```

### Phase 3: Generate Recommendations

Categorize findings into three types:

| Category | Description | Typical Action |
|----------|-------------|----------------|
| **Spec Additions** | Patterns that should be documented | Add to relevant spec doc |
| **Spec Reshaping** | Code that needs to conform to existing spec | Extend interface/options, refactor |
| **Simplifications** | Complexity that can be reduced | Consolidate, remove indirection |

**For each recommendation, provide:**
- Clear description of the issue
- File:line citations for evidence
- Specific spec reference (for deviations)
- Suggested action
- Risk assessment (low/medium/high)

### Phase 4: Write Analysis and Create Tasks

**Write analysis to `.ralph/refactor-plans/<MODULE>-<timestamp>.md`.**

See references/analysis-framework.md for output format.

**Present prioritized recommendations and ask for selection:**

```yaml
questions:
  - question: Which recommendations should become kanban tasks?
    header: Create tasks
    multiSelect: true
    options:
      - label: <Finding 1 summary>
        description: "<Type>: Brief description"
      - label: <Finding 2 summary>
        description: "<Type>: Brief description"
      # ... dynamically generated from analysis
```

**Ask for task priority:**

```yaml
questions:
  - question: What priority for selected refactoring tasks?
    header: Priority
    options:
      - label: HIGH
        description: Block other work, do immediately
      - label: MEDIUM
        description: Important but not blocking
      - label: LOW
        description: Nice to have, do when convenient
```

**Create tasks for selected recommendations** - either invoke `/kanban` or create tasks directly.

## Example

**User**: `/wiggum-refactor lib/pipeline/`

**Assistant**: I'll analyze the `lib/pipeline/` module for refactoring opportunities. Let me start by discovering spec documents.

*[Uses Glob to find *.md files in docs/ and root]*

Found spec documents:
- `docs/ARCHITECTURE.md`
- `docs/PIPELINE-SCHEMA.md`
- `docs/PROTOCOL.md`
- `CLAUDE.md`

*[Uses AskUserQuestion]*
```yaml
questions:
  - question: What is your primary refactoring goal?
    header: Goal
    options:
      - label: All of the above (Recommended)
        description: Comprehensive analysis
      - label: Spec compliance
        description: Ensure code matches specifications
      - label: Pattern extraction
        description: Identify reusable patterns
      - label: Simplification
        description: Reduce complexity
```

**User selects**: All of the above

**Assistant**: I'll do a comprehensive analysis. Let me examine the module.

*[Uses Glob to list files in lib/pipeline/]*
*[Uses Read to examine loader.sh, runner.sh]*
*[Uses Grep to find function definitions, error patterns]*

Found 5 files with 847 total lines. Now comparing against specs...

*[Uses Read to examine docs/PIPELINE-SCHEMA.md]*

**Pattern Mining Results:**
- Found error handling pattern repeated in 4 functions with slight variations
- Found logging convention used inconsistently (some use `log_info`, some use `echo`)

**Spec Comparison Results:**
- `runner.sh:145` uses `on_error: abort` but spec says `on_error: fail` is default
- `loader.sh:78` adds undocumented `skip_validation` option

**Complexity Assessment:**
- `runner.sh` has 3 functions over 50 lines each
- Circular dependency between loader and runner for validation

*[Uses AskUserQuestion for deviation handling]*

```yaml
questions:
  - question: loader.sh adds 'skip_validation' option not in spec. How to handle?
    header: Deviation
    options:
      - label: Extend spec
        description: Add skip_validation as documented option
      - label: Flag as tech debt
        description: Track for review, not urgent
```

**User selects**: Extend spec

**Assistant**: I'll recommend adding it to the spec. Let me compile the full analysis.

*[Writes to .ralph/refactor-plans/pipeline-1706540000.md]*

Analysis complete. Here are my recommendations:

### Spec Additions (1)
1. **Error handling pattern** - Extract common retry logic to spec

### Spec Reshaping (2)
2. **Fix on_error default** - runner.sh:145 should use `fail` not `abort`
3. **Document skip_validation** - Add to PIPELINE-SCHEMA.md

### Simplifications (2)
4. **Consolidate logging** - Standardize on `log_*` functions
5. **Break up run_pipeline()** - Function at 87 lines, split into phases

*[Uses AskUserQuestion for task selection]*

```yaml
questions:
  - question: Which recommendations should become kanban tasks?
    header: Create tasks
    multiSelect: true
    options:
      - label: Fix on_error default
        description: "Reshaping: Align runner.sh with spec default"
      - label: Document skip_validation
        description: "Spec addition: Add to PIPELINE-SCHEMA.md"
      - label: Consolidate logging
        description: "Simplification: Standardize log functions"
      - label: Break up run_pipeline
        description: "Simplification: Split 87-line function"
```

**User selects**: Fix on_error default, Consolidate logging

**Assistant**: I'll create tasks for those 2 items. What priority?

*[Uses AskUserQuestion for priority]*

**User selects**: MEDIUM

**Assistant**: I'll create the kanban tasks now.

*[Creates tasks or invokes /kanban]*

Created 2 tasks:
- `REFAC-001`: Fix on_error default value in runner.sh (MEDIUM)
- `REFAC-002`: Consolidate logging to standard log_* functions (MEDIUM)

Full analysis saved to `.ralph/refactor-plans/pipeline-1706540000.md`.

## Key Principles

1. **Evidence-based** - Every recommendation cites specific files and lines
2. **Spec-grounded** - Deviations always reference the authoritative spec
3. **User-driven** - User chooses which findings become tasks
4. **Behavior-preserving** - Refactoring doesn't change what code does
5. **Progressive** - Ask questions as needed, don't overwhelm upfront

## Progressive Disclosure

This SKILL.md contains the core workflow. For detailed guidance:
- **Analysis methodology**: references/analysis-framework.md
- **Deviation patterns**: references/spec-deviation-patterns.md
- **Pattern extraction**: references/generalization-strategies.md
