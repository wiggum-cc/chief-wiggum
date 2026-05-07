# Spec Deviation Patterns

Common types of specification deviations and strategies for reshaping code to comply.

## Types of Deviations

### 1. Extra Parameters

**Pattern**: Code accepts parameters not defined in the spec.

```bash
# Spec says:
#   agent_run(worker_dir, project_dir)
#
# Code has:
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local verbose="${3:-false}"  # <- Not in spec
}
```

**Detection**: Compare function signatures against spec definitions.

**Resolution Options**:
| Option | When to Use |
|--------|-------------|
| Remove parameter | Parameter is unused or can be derived |
| Extend spec | Parameter is genuinely useful, document it |
| Make internal | Move to internal helper, keep public interface clean |

### 2. Missing Required Behavior

**Pattern**: Code doesn't implement behavior the spec requires.

```markdown
# Spec says:
"All agents must log start and end times to activity.jsonl"

# Code does:
agent_run() {
    # Does work but never logs to activity.jsonl
}
```

**Detection**: Search for spec keywords ("must", "required", "always") and verify implementation.

**Resolution**: Implement the missing behavior. This is almost always a code fix, not a spec change.

### 3. Different Default Values

**Pattern**: Code uses different defaults than spec defines.

```bash
# Spec says:
#   "max_iterations defaults to 5"
#
# Code has:
local max_iterations="${AGENT_MAX_ITERATIONS:-10}"  # <- Wrong default
```

**Detection**: Look for hardcoded values and compare against spec.

**Resolution Options**:
| Option | When to Use |
|--------|-------------|
| Fix code | Spec default is intentional |
| Update spec | Code default is better (document why) |
| Parameterize | Allow override via config |

### 4. Wrong Error Handling

**Pattern**: Code handles errors differently than spec describes.

```bash
# Spec says:
#   "On validation failure, return exit code 2"
#
# Code does:
if ! validate_input "$input"; then
    log_error "Validation failed"
    return 1  # <- Should be 2
fi
```

**Detection**: Search for error handling code and verify against spec exit codes.

**Resolution**: Align code with spec. Error contracts are critical for integration.

### 5. Naming Inconsistencies

**Pattern**: Code uses different terminology than spec.

```bash
# Spec says: "task" throughout
# Code says:
local job_id="$1"      # Should be task_id
local job_status=...   # Should be task_status
```

**Detection**: Grep for spec terminology and note mismatches.

**Resolution**: Rename to match spec. Naming consistency reduces cognitive load.

### 6. Ordering Violations

**Pattern**: Code performs operations in different order than spec.

```markdown
# Spec says:
"Pipeline steps execute in order: validate → transform → persist"

# Code does:
transform_data
validate_input   # <- Out of order
persist_result
```

**Detection**: Trace execution flow and compare against spec sequence.

**Resolution**: Reorder operations to match spec. Order often matters for correctness.

### 7. Scope Creep

**Pattern**: Code does more than spec describes.

```bash
# Spec says:
#   "loader.sh reads pipeline config from JSON file"
#
# Code also:
- Validates the config (not in spec)
- Caches parsed results (not in spec)
- Sends telemetry (not in spec)
```

**Detection**: List all behaviors in code and check each against spec.

**Resolution Options**:
| Option | When to Use |
|--------|-------------|
| Extend spec | Behavior is valuable, document it |
| Extract | Move to separate module with its own spec |
| Remove | Behavior is truly unnecessary |

### 8. Different Return Values

**Pattern**: Code returns values/types not matching spec.

```bash
# Spec says:
#   "Returns: JSON object with keys: status, message"
#
# Code returns:
echo "$status"  # <- Just a string, not JSON
```

**Detection**: Check return statements against spec contracts.

**Resolution**: Restructure output to match spec. Return contracts are API promises.

## Reshaping Strategies

### Strategy 1: Extend the Interface

When code adds useful functionality not in spec, extend the spec rather than remove code.

**Before**:
```bash
# Spec: parse_config(file_path)
# Code: parse_config(file_path, strict_mode)
```

**After** (spec update):
```markdown
## parse_config

Args:
- file_path: Path to config file
- strict_mode: (optional, default: false) When true, fail on unknown keys
```

### Strategy 2: Add Options Object

When too many optional parameters accumulate, consolidate into options.

**Before**:
```bash
run_agent(dir, project, verbose, dry_run, timeout, retry_count)
```

**After**:
```bash
# Spec defines options structure
run_agent(dir, project, options)
# options: { verbose, dry_run, timeout, retry_count }
```

### Strategy 3: Split Function

When a function does too much vs spec, split into focused functions.

**Before**:
```bash
# Spec: process_task(task) - validates and executes task
# Code: process_task also logs, retries, and sends notifications
```

**After**:
```bash
validate_task(task)
execute_task(task)
notify_completion(task)  # If worthy of spec, add it
```

### Strategy 4: Create Variants

When code needs different behavior for different contexts, create spec variants.

**Before**:
```bash
# Spec: save_result(data)
# Code: save_result has special handling for "audit" type
```

**After** (spec update):
```markdown
## save_result

Standard result saving.

## save_audit_result

Specialized saving for audit results with additional metadata.
```

### Strategy 5: Document as Extension Point

When behavior is intentionally customizable, document it as an extension.

**Before**:
```bash
# Spec says nothing about hooks
# Code calls pre_run_hook() and post_run_hook()
```

**After** (spec update):
```markdown
## Extension Points

### pre_run_hook()
Called before agent execution. Override for custom setup.

### post_run_hook()
Called after agent execution. Override for custom teardown.
```

## Severity Assessment

Categorize deviations by impact:

| Severity | Criteria | Action |
|----------|----------|--------|
| **Critical** | Breaks integration, security risk, data loss | Fix immediately |
| **High** | Causes incorrect behavior in edge cases | Schedule fix |
| **Medium** | Inconsistent but functional | Add to backlog |
| **Low** | Cosmetic, naming only | Fix opportunistically |

## Common Causes

Understanding why deviations occur helps prevent future ones:

1. **Spec written after code** - Code evolved, spec wasn't updated
2. **Multiple contributors** - Different interpretations of spec
3. **Emergency fixes** - Quick patches that bypass spec
4. **Feature creep** - Incremental additions without spec review
5. **Copy-paste drift** - Code copied and modified without updating both
6. **Stale spec** - Requirements changed but spec wasn't updated

## Verification After Reshaping

After fixing a deviation:

1. **Re-read spec** - Confirm fix matches
2. **Run tests** - Ensure no regression
3. **Check callers** - Verify consumers still work
4. **Update docs** - If spec was extended, document it
5. **Add test** - Prevent regression of this specific deviation
