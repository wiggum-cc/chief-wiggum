# Kanban Board with Circular Dependencies

## TASKS

- [ ] **[TASK-001]** Task A depends on C
  - Description: Creates circular dependency A -> C -> B -> A
  - Priority: HIGH
  - Dependencies: TASK-003

- [ ] **[TASK-002]** Task B depends on A
  - Description: Part of circular dependency chain
  - Priority: MEDIUM
  - Dependencies: TASK-001

- [ ] **[TASK-003]** Task C depends on B
  - Description: Part of circular dependency chain
  - Priority: LOW
  - Dependencies: TASK-002
