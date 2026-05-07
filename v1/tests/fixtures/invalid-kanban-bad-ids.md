# Invalid Kanban - Bad Task IDs

## TASKS

- [ ] **[T-001]** ID too short (prefix < 2 chars)
  - Description: Task ID prefix must be 2-10 characters
  - Priority: HIGH
  - Dependencies: none

- [ ] **[VERYLONGPREFIX-001]** ID prefix too long (> 10 chars)
  - Description: Task ID prefix must be 2-10 characters
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-abc]** Non-numeric ID
  - Description: Task ID number must be numeric
  - Priority: MEDIUM
  - Dependencies: none

- [ ] **[TASK-12345]** Number too long (> 4 digits)
  - Description: Task ID number must be 1-4 digits
  - Priority: MEDIUM
  - Dependencies: none
