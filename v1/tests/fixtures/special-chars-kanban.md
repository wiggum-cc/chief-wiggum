# Kanban with Special Characters

## TASKS

- [ ] **[TASK-001]** Handle special chars: $ " ' ` \
  - Description: Test task with special shell characters: $var, "quotes", 'single', `backticks`, \backslash
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-002]** Process pipe | and redirect >
  - Description: Ensure tasks handle pipe | redirect > append >> and other shell operators safely
  - Priority: MEDIUM
  - Dependencies: TASK-001

- [ ] **[TASK-003]** Support ampersand & and semicolon ;
  - Description: Task description with background & and command chaining ; operators
  - Priority: LOW
  - Dependencies: none
  - Scope:
    - Test command: echo "hello" > file.txt
    - Test variable: export VAR="value with spaces"
    - Test escaping: echo 'single "double" `backtick`'

- [ ] **[TASK-004]** Unicode and emoji support 🚀
  - Description: Task with unicode characters: café, naïve, 日本語, and emojis 🎯 ✅ 🚀
  - Priority: MEDIUM
  - Dependencies: none
