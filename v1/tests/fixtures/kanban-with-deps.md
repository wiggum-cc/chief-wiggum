# Kanban Board with Dependencies

## TASKS

- [x] **[TASK-001]** Completed dependency task
  - Description: This task has been completed
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-002]** Ready task with satisfied dependency
  - Description: This task depends on TASK-001 which is complete
  - Priority: MEDIUM
  - Dependencies: TASK-001

- [ ] **[TASK-003]** Blocked task with unsatisfied dependency
  - Description: This task depends on TASK-002 which is not complete
  - Priority: HIGH
  - Dependencies: TASK-002

- [ ] **[TASK-004]** Task with multiple dependencies
  - Description: This task depends on multiple tasks
  - Priority: LOW
  - Dependencies: TASK-001, TASK-002

- [=] **[TASK-005]** In-progress task
  - Description: This task is currently being worked on
  - Priority: MEDIUM
  - Dependencies: TASK-001
