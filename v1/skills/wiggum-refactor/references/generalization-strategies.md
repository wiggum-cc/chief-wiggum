# Generalization Strategies

How to identify patterns worthy of spec promotion and extract them effectively.

## Identifying Generalizable Patterns

### The Rule of Three

A pattern is a candidate for generalization when:
- It appears in **3+ files** within the module
- It solves the **same conceptual problem** each time
- It has **similar structure** (not just similar code)

```
1 occurrence  → Specific solution, leave it alone
2 occurrences → Coincidence, watch for more
3+ occurrences → Pattern, consider generalizing
```

### Pattern Recognition Checklist

When evaluating a repeated structure, ask:

| Question | If Yes | If No |
|----------|--------|-------|
| Is it solving a common problem? | Generalize | May be coincidental |
| Would other modules benefit? | Add to project spec | Module-local convention |
| Is the structure stable? | Ready to document | Let it mature first |
| Does variation add value? | Document variants | Enforce one approach |

### Types of Generalizable Patterns

**1. Interface Patterns**
Functions with consistent signatures across files.

```bash
# Pattern: all agents implement this signature
agent_run(worker_dir, project_dir)
# Returns: 0=PASS, 10=FAIL, 12=MAX_ITERATIONS
```
→ Document as formal interface in agent spec.

**2. Error Handling Patterns**
Consistent approaches to failures.

```bash
# Pattern: retry with exponential backoff
for attempt in 1 2 3; do
    if operation; then break; fi
    sleep $((attempt * 2))
done
```
→ Document as standard retry strategy.

**3. Data Format Patterns**
Consistent structures for passing data.

```bash
# Pattern: result files are NDJSON with timestamp
echo '{"ts":"2024-01-15T10:00:00Z","event":"start"}' >> activity.jsonl
```
→ Document as data format specification.

**4. Lifecycle Patterns**
Consistent phases in processing.

```bash
# Pattern: all processors follow validate → transform → persist
validate_input "$data"
transformed=$(transform "$data")
persist_result "$transformed"
```
→ Document as lifecycle contract.

**5. Naming Conventions**
Emergent naming patterns.

```bash
# Pattern: predicates prefixed with is_ or has_
is_valid_task()
has_pending_dependencies()
is_worker_running()
```
→ Document as naming convention.

## When NOT to Generalize

Not every repeated code should become a spec. Avoid generalizing:

### Context-Specific Solutions

Code that looks similar but solves different problems.

```bash
# File 1: Parsing user input
read -r input
trimmed="${input## }"

# File 2: Parsing file paths
read -r path
trimmed="${path## }"
```

Same syntax, different purposes. Keep separate.

### Premature Patterns

Patterns that haven't stabilized yet.

```bash
# Version 1 (last week)
handle_error() { log_error "$1"; return 1; }

# Version 2 (yesterday)
handle_error() { log_error "$1"; notify_admin; return 1; }

# Version 3 (today)
handle_error() { log_error "$1"; notify_admin; cleanup; return 1; }
```

Still evolving. Wait for stability before documenting.

### One-Off Variations

When each instance has meaningful differences.

```bash
# File 1: Retry 3 times, 2-second delay
# File 2: Retry 5 times, 10-second delay
# File 3: Retry 1 time, no delay
```

The numbers aren't arbitrary - they fit their contexts. Don't force uniformity.

### Implementation Details

Internal mechanics that callers don't need to know.

```bash
# How we cache internally
_cache_result() {
    local key="$1" value="$2"
    echo "$value" > "/tmp/cache/$key"
}
```

This is implementation, not interface. Don't spec it.

## Extraction Process

### Step 1: Collect Examples

Gather all instances of the pattern:

```markdown
## Pattern: Agent Result Writing

### Instance 1: lib/agents/system/task-worker.sh:145
```bash
echo "PASS" > "$worker_dir/gate_result"
```

### Instance 2: lib/agents/engineering/security-audit.sh:89
```bash
echo "FIX" > "$worker_dir/gate_result"
```

### Instance 3: lib/agents/product/plan-mode.sh:112
```bash
echo "FAIL" > "$worker_dir/gate_result"
```
```

### Step 2: Identify Core vs Variation

Separate what's consistent from what varies:

```markdown
## Core (always the same)
- Writes to `$worker_dir/gate_result`
- Uses echo redirection
- Single word value

## Variation (differs between instances)
- The actual value: PASS, FAIL, FIX, SKIP
```

### Step 3: Draft Spec Language

Write clear, actionable spec text:

```markdown
## Gate Results

Agents signal their outcome by writing to `gate_result`.

### Format
```
$worker_dir/gate_result
```

### Values
| Value | Meaning | Exit Code |
|-------|---------|-----------|
| PASS | Success | 0 |
| FAIL | Failure | 10 |
| FIX | Partial, needs retry | 0 |
| SKIP | Intentionally skipped | 0 |

### Example
```bash
echo "PASS" > "$worker_dir/gate_result"
```
```

### Step 4: Validate Against Instances

Check that your spec covers all collected examples:

- [ ] Instance 1 matches spec? Yes - writes PASS
- [ ] Instance 2 matches spec? Yes - writes FIX
- [ ] Instance 3 matches spec? Yes - writes FAIL

### Step 5: Identify Placement

Determine which spec document should contain this:

| Pattern Type | Typical Location |
|--------------|------------------|
| Agent interfaces | AGENT_DEV_GUIDE.md |
| Data formats | PROTOCOL.md |
| Pipeline behavior | PIPELINE-SCHEMA.md |
| General conventions | ARCHITECTURE.md or CLAUDE.md |
| Project-specific | .ralph/config docs |

## Spec Writing Guidelines

### Be Precise

Bad: "Agents should write results to a file."
Good: "Agents must write exactly one of {PASS, FAIL, FIX, SKIP} to `$worker_dir/gate_result`."

### Include Examples

Every spec section should have at least one concrete example:

```markdown
## Logging

Use the standard log functions for output.

### Example
```bash
log_info "Starting agent"
log_error "Validation failed: $reason"
log_debug "Processing item $i of $total"
```
```

### Document Rationale

Explain why, not just what:

```markdown
## Epoch-Named Results

Result files use epoch timestamps in their names.

**Rationale**: Multiple runs of the same agent produce distinct files,
preventing data loss and enabling history tracking.

**Format**: `<agent>-<epoch>.json` (e.g., `security-audit-1706540000.json`)
```

### Specify Boundaries

Be clear about scope:

```markdown
## Error Handling

This section applies to **agent-level** errors only.
For pipeline-level error handling, see PIPELINE-SCHEMA.md.
```

## After Generalization

Once a pattern is added to spec:

1. **Communicate** - Inform team of new spec section
2. **Verify existing code** - Check all instances comply
3. **Add tests** - Automated checks for spec compliance
4. **Update related patterns** - New code should follow the spec
5. **Monitor** - Watch for future drift

## Generalization Anti-Patterns

### Over-Specification

Speccing every detail removes flexibility:

```markdown
# Too specific
"Log messages must be exactly 80 characters or less,
start with a timestamp in ISO8601 format,
include the function name in brackets..."
```

Leave room for judgment.

### Forced Uniformity

Making things identical that should differ:

```markdown
# Bad: Forcing same retry count everywhere
"All operations retry exactly 3 times"

# Better: Establishing pattern with flexibility
"Operations should implement retry with backoff.
Default: 3 retries. Adjust based on operation cost."
```

### Spec Without Enforcement

Documentation nobody follows is worse than none:

```markdown
# In spec for 6 months, never enforced
"All functions must have JSDoc comments"

# Meanwhile in codebase
function doThing() { ... }  // No comment
```

Only spec what you'll actually maintain.
