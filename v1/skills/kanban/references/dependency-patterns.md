# Dependency Patterns Reference

## Dependency Rules

1. **Only `[x]` satisfies** - Tasks in `[P]` (Pending Approval) do NOT satisfy dependencies
2. **Must exist** - Only reference tasks that exist in kanban
3. **No cycles** - A cannot depend on B if B depends on A
4. **Explicit** - Always specify, use `none` if no dependencies

## Common Patterns

### Sequential Chain
```
TASK-001 → TASK-002 → TASK-003
```
Each task depends on the previous.

```markdown
- [ ] **[TASK-001]** Create database schema
  - Dependencies: none

- [ ] **[TASK-002]** Create data models
  - Dependencies: TASK-001

- [ ] **[TASK-003]** Create API endpoints
  - Dependencies: TASK-002
```

### Parallel with Merge
```
TASK-001 ─┬─ TASK-002 ─┬─ TASK-004
          └─ TASK-003 ─┘
```
Independent tasks merge at a common dependent.

```markdown
- [ ] **[TASK-001]** Setup project structure
  - Dependencies: none

- [ ] **[TASK-002]** Create frontend components
  - Dependencies: TASK-001

- [ ] **[TASK-003]** Create backend API
  - Dependencies: TASK-001

- [ ] **[TASK-004]** Integrate frontend with backend
  - Dependencies: TASK-002, TASK-003
```

### Diamond
```
       TASK-001
      /        \
TASK-002    TASK-003
      \        /
       TASK-004
```

```markdown
- [ ] **[TASK-001]** Core utilities
  - Dependencies: none

- [ ] **[TASK-002]** Auth module (uses utilities)
  - Dependencies: TASK-001

- [ ] **[TASK-003]** User module (uses utilities)
  - Dependencies: TASK-001

- [ ] **[TASK-004]** Dashboard (uses auth + user)
  - Dependencies: TASK-002, TASK-003
```

### External Dependency
When depending on a task in `[P]` status:

```markdown
- [ ] **[TASK-015]** Auth routes
  - Dependencies: TASK-010
  # Note: TASK-010 is [P], won't start until PR merged
```

Document this in the task or dependency graph.

## Visualizing Dependencies

Always show a dependency graph when presenting multiple tasks:

```
TASK-008 [x] ─── TASK-013 ─┬─ TASK-014 ─┬─ TASK-015
                           └────────────┘
TASK-010 [P] ─────────────────────────────┘
```

Include status markers to show blocking tasks.

## Anti-Patterns

### Circular Dependency
```markdown
# WRONG - creates deadlock
- [ ] **[TASK-001]** Feature A
  - Dependencies: TASK-002

- [ ] **[TASK-002]** Feature B
  - Dependencies: TASK-001
```

### Missing Dependency
```markdown
# WRONG - TASK-002 uses auth but doesn't depend on it
- [ ] **[TASK-001]** Create auth middleware
  - Dependencies: none

- [ ] **[TASK-002]** Create protected endpoint
  - Dependencies: none  # Should depend on TASK-001
```

### Over-Depending
```markdown
# WRONG - too many dependencies slow execution
- [ ] **[TASK-010]** Final integration
  - Dependencies: TASK-001, TASK-002, TASK-003, TASK-004, TASK-005, TASK-006
  # Consider: which are truly required vs nice-to-have?
```
