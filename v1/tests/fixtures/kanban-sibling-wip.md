# Kanban Board for Sibling WIP Penalty Testing

## TASKS

- [=] **[FEAT-001]** In progress feature task
  - Description: Currently being worked on
  - Priority: MEDIUM
  - Dependencies: none

- [P] **[BUG-001]** Pending approval bug fix
  - Description: Waiting for review
  - Priority: MEDIUM
  - Dependencies: none

- [*] **[REFAC-001]** Failed refactoring task
  - Description: Previously attempted, needs retry
  - Priority: MEDIUM
  - Dependencies: none

- [ ] **[FEAT-002]** Pending feature task (should be penalized - sibling in-progress)
  - Description: Same prefix as in-progress task
  - Priority: HIGH
  - Dependencies: none

- [ ] **[BUG-002]** Pending bug fix (should be penalized - sibling pending approval)
  - Description: Same prefix as pending approval task
  - Priority: HIGH
  - Dependencies: none

- [ ] **[REFAC-002]** Pending refactoring (should be penalized - sibling failed)
  - Description: Same prefix as failed task
  - Priority: HIGH
  - Dependencies: none

- [ ] **[OTHER-001]** Unrelated high priority task
  - Description: Different prefix, should not be penalized
  - Priority: HIGH
  - Dependencies: none

- [ ] **[OTHER-002]** Unrelated medium priority task
  - Description: Different prefix, should not be penalized
  - Priority: MEDIUM
  - Dependencies: none
