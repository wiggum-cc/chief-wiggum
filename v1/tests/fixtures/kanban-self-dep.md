# Kanban Board with Self-Dependency

## TASKS

- [ ] **[TASK-001]** Normal task with no deps
  - Description: A normal task
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-002]** Task depends on itself
  - Description: Task with self-dependency
  - Priority: MEDIUM
  - Dependencies: TASK-002

- [ ] **[TASK-003]** Another normal task
  - Description: Depends on normal task
  - Priority: LOW
  - Dependencies: TASK-001
