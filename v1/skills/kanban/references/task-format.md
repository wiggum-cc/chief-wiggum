# Task Format Reference

## Task Entry Structure

```markdown
- [ ] **[TASK-ID]** Brief task description
  - Description: Detailed description of what needs to be done
  - Priority: CRITICAL|HIGH|MEDIUM|LOW
  - Complexity: HIGH|MEDIUM|LOW (optional)
  - Dependencies: TASK-ID-1, TASK-ID-2 | none
  - Scope:
    - Specific deliverable item
    - Another deliverable
  - Out of Scope:
    - Thing NOT to implement
  - Acceptance Criteria:
    - Validation point
```

## Field Specifications

### Task ID
- **Pattern**: `[A-Za-z]{2,10}-[0-9]{1,4}`
- **Examples**: `[TASK-001]`, `[FEATURE-042]`, `[BUG-123]`
- Prefix: 2-10 letters
- Number: 1-4 digits
- Must be unique across the kanban file
- Wrapped in brackets and bold: `**[TASK-ID]**`

### Status Checkbox

| Marker | Status | Description |
|--------|--------|-------------|
| `- [ ]` | Pending | Not started |
| `- [=]` | In-progress | Worker actively processing |
| `- [P]` | Pending Approval | PR created, awaiting merge |
| `- [x]` | Complete | PR merged |
| `- [N]` | Not Planned | Won't be done |
| `- [*]` | Failed | Worker encountered errors |

**Dependency Resolution**: Only `[x]` (Complete) satisfies dependencies. `[P]` does NOT.

### Brief Description
- Immediately after task ID on same line
- Under 80 characters
- Imperative statement ("Create X" not "Creating X")
- Used in commit messages and PR titles

### Priority (Required)
- **CRITICAL**: Security vulnerabilities, data loss, system-breaking
- **HIGH**: Blocking other work, critical bugs, foundational
- **MEDIUM**: Important features, non-critical bugs
- **LOW**: Nice-to-haves, optimizations, documentation

### Complexity (Optional)
- **HIGH**: Large scope, many files, architectural changes
- **MEDIUM**: Moderate scope, several files
- **LOW**: Small scope, few files, straightforward

### Dependencies (Required)
- Comma-separated task IDs or `none`
- Only reference existing tasks
- Consider technical and logical dependencies

### Scope (Optional)
- 2-space indent: `  - Scope:`
- Items at 4-space indent: `    - Item`
- Becomes checklist in worker PRD
- Break complex tasks into deliverables

### Out of Scope (Optional)
- Clarify boundaries
- Prevent scope creep
- List exclusions explicitly

### Acceptance Criteria (Optional)
- Define success criteria
- Validation points
- Testable conditions

## Common Pitfalls

### Wrong Indentation
```markdown
# Wrong
- [ ] **[TASK-001]** Do something
- Description: Details

# Correct
- [ ] **[TASK-001]** Do something
  - Description: Details
```

### Missing Required Fields
```markdown
# Wrong (missing Priority and Dependencies)
- [ ] **[TASK-001]** Do something
  - Description: Details

# Correct
- [ ] **[TASK-001]** Do something
  - Description: Details
  - Priority: MEDIUM
  - Dependencies: none
```

### Invalid Task ID
```markdown
# Wrong
- [ ] **TASK-001** Do something        # missing brackets
- [ ] **[T-1]** Do something           # prefix too short
- [ ] **[VERYLONGPREFIX-001]** Do something # prefix too long

# Correct
- [ ] **[TASK-001]** Do something
- [ ] **[FEAT-1]** Do something
```
