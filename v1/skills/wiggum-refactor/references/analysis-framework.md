# Analysis Framework

Systematic guidance for analyzing modules during refactoring analysis.

## Discovering Spec Documents

### Where to Look

1. **Project root**: `README.md`, `CLAUDE.md`, `CONTRIBUTING.md`
2. **docs/ directory**: `docs/*.md`, `docs/**/*.md`
3. **Module-specific**: Check for `<module>/README.md` or `<module>/SPEC.md`

### Identifying Authoritative Specs

Not all markdown files are specs. Look for:

| Indicator | Example |
|-----------|---------|
| Defines interfaces | "Functions must return..." |
| Specifies behavior | "On error, the system should..." |
| Documents conventions | "All files use snake_case naming" |
| Lists requirements | "Required fields: ..." |

Skip files that are:
- Pure documentation (user guides, tutorials)
- Changelogs, release notes
- Auto-generated API docs

### Mapping Modules to Specs

Build a mental map of which specs govern which modules:

```
lib/pipeline/ → docs/PIPELINE-SCHEMA.md, docs/ARCHITECTURE.md
lib/agents/   → docs/AGENT_DEV_GUIDE.md, config/agents.json
lib/git/      → docs/PROTOCOL.md (for inter-component communication)
```

## Pattern Recognition Techniques

### Function Signature Analysis

Look for repeated signatures across files:

```bash
# Same parameter patterns
function_a(worker_dir, project_dir)
function_b(worker_dir, project_dir)
function_c(worker_dir, project_dir)

# Same return conventions
# Returns: 0=success, 10=failure, 12=max_iterations
```

### Error Handling Patterns

Common patterns to look for:

1. **Try-catch structures** in different files
2. **Retry logic** with similar backoff strategies
3. **Fallback behaviors** when operations fail
4. **Logging conventions** for errors

### Data Flow Patterns

Track how data moves through the module:

1. **Input validation** - Where and how inputs are checked
2. **Transformation** - How data is processed
3. **Output format** - How results are structured
4. **State management** - Where state is stored and accessed

### Naming Conventions

Look for emergent conventions:

| Pattern | Example | Action |
|---------|---------|--------|
| Consistent prefix | `parse_*`, `validate_*` | May indicate implicit interface |
| Inconsistent naming | `get_user` vs `fetch_user` | Candidate for standardization |
| Spec terminology mismatch | Code says "task" but spec says "job" | Needs alignment |

## Complexity Metrics

### Quantitative Measures

Gather these metrics for the module:

| Metric | How to Measure | Concern Threshold |
|--------|----------------|-------------------|
| Files | Count in module | >15 files |
| Lines per file | `wc -l` | >300 lines |
| Functions per file | Count definitions | >10 functions |
| Lines per function | Count between function start/end | >50 lines |
| Parameters per function | Count arguments | >5 params |

### Qualitative Indicators

Look for these complexity smells:

1. **Deep nesting** - More than 3 levels of indentation
2. **Long parameter lists** - Functions taking many arguments
3. **Global state** - Variables accessed across functions without passing
4. **Circular dependencies** - Module A imports B, B imports A
5. **God functions** - One function doing too many things
6. **Premature abstraction** - Abstraction used in only one place

### Coupling Analysis

Identify how tightly files are connected:

```
High coupling indicators:
- File A sources/imports file B
- File A calls functions from file B
- File A reads state written by file B
- File A assumes file B ran first
```

## Structuring Findings

### For Each Pattern Found

Document:
- **What**: Brief description of the pattern
- **Where**: File:line citations (at least 2 examples)
- **Frequency**: How many times it appears
- **Recommendation**: Add to spec, leave as-is, or consolidate

### For Each Deviation Found

Document:
- **Spec reference**: "docs/SPEC.md section X says..."
- **Code location**: file:line where deviation occurs
- **Nature**: What spec says vs what code does
- **Severity**: How much this affects correctness/maintainability
- **Recommendation**: Reshape code, update spec, or extend spec

### For Each Simplification Opportunity

Document:
- **Current state**: What complexity exists
- **Proposed change**: How to simplify
- **Risk**: What could go wrong
- **Benefit**: Why this is worth doing

## Output File Format

Write analysis to `.ralph/refactor-plans/<MODULE>-<timestamp>.md`:

```markdown
# Refactoring Analysis: <module-path>

## Summary
- **Files analyzed**: N
- **Total lines**: N
- **Spec documents referenced**: docs/X.md, docs/Y.md
- **Analysis focus**: [compliance|extraction|simplification|all]

## 1. Spec Additions (Patterns to Generalize)

### Pattern: <name>
- **Found in**: file1.sh:L10, file2.sh:L45, file3.sh:L20
- **Description**: [What the pattern does]
- **Recommendation**: Add to docs/<spec>.md as [interface/protocol/constraint]
- **Draft spec text**:
  ```
  [Suggested addition to spec]
  ```

## 2. Spec Deviations (Code to Reshape)

### Deviation: <name>
- **Location**: file.sh:L20-50
- **Spec requirement**: "docs/SPEC.md says: [quote]"
- **Current behavior**: [What code actually does]
- **Recommendation**: [How to reshape - extend interface/add option/fix code]

## 3. Simplification Opportunities

### Area: <name>
- **Files affected**: file1.sh, file2.sh
- **Current state**: [Description of complexity]
- **Recommendation**: [How to simplify]
- **Risk**: [Low/Medium/High - what could break]

## Suggested Kanban Tasks

| # | Task | Category | Priority | Complexity |
|---|------|----------|----------|------------|
| 1 | [Brief description] | Reshaping | HIGH | Low |
| 2 | [Brief description] | Simplification | MEDIUM | Medium |

## Verification Checklist

After implementing recommendations:
- [ ] Run existing tests
- [ ] Verify spec documents updated where needed
- [ ] Check no functionality removed unintentionally
- [ ] Review for new coupling introduced
```

## Iteration Strategy

Analysis is iterative. Expect to:

1. **First pass**: Gather metrics, identify obvious patterns
2. **Second pass**: Deep dive into interesting findings
3. **Ask questions**: Clarify user intent when patterns are ambiguous
4. **Refine**: Adjust recommendations based on user feedback
5. **Finalize**: Write analysis file and present task options

Don't try to find everything in one pass. Surface the most impactful findings first, then dig deeper as needed.
