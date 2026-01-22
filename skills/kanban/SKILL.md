---
name: kanban
description: Generate Kanban task entries for Chief Wiggum
---

# Kanban Task Generator

Generate properly formatted task entries for Chief Wiggum's `.ralph/kanban.md` file.

## Task Entry Format

```markdown
- [ ] **[TASK-ID]** Brief task description
  - Description: Detailed description of what needs to be done
  - Priority: CRITICAL|HIGH|MEDIUM|LOW
  - Complexity: HIGH|MEDIUM|LOW (optional)
  - Dependencies: TASK-ID-1, TASK-ID-2 | none
```

### Optional Extended Fields

```markdown
  - Scope:
    - Specific item to implement or deliver
    - Another item in scope
  - Out of Scope:
    - Thing NOT to implement
    - Another exclusion
  - Acceptance Criteria:
    - Validation point 1
    - Validation point 2
```

## Field Specifications

### Task ID

- **Format**: `[PREFIX-NUMBER]`
- **Pattern**: `[A-Za-z]{2,8}-[0-9]+`
- **Examples**: `[TASK-001]`, `[FEATURE-042]`, `[BUG-123]`
- Prefix: 2-8 uppercase letters
- Number: One or more digits
- Must be unique across the kanban file
- Wrapped in square brackets and bold: `**[TASK-ID]**`

### Status Checkbox

| Marker | Status | Description |
|--------|--------|-------------|
| `- [ ]` | Pending | Not started |
| `- [=]` | In-progress | Worker actively processing |
| `- [P]` | Pending Approval | PR created, awaiting review/merge |
| `- [x]` | Complete | PR merged, task finished |
| `- [N]` | Not Planned | Task won't be done |
| `- [*]` | Failed | Worker encountered errors |

**Dependency Resolution**: Tasks only satisfy dependencies when they reach `[x]` (Complete/Merged) status. Tasks in `[P]` (Pending Approval) do NOT satisfy dependencies.

### Brief Description

- Appears immediately after the task ID on the same line
- Should be concise (under 80 characters)
- Used in commit messages, PR titles, and changelogs
- Written as an imperative statement (e.g., "Create README file" not "Creating README")

### Description (Required)

- Indented with 2 spaces: `  - Description:`
- Provides detailed context about what needs to be implemented
- Should be specific enough for a worker to understand requirements

### Priority (Required)

- Indented with 2 spaces: `  - Priority:`
- Valid values (case-sensitive, uppercase):
  - **CRITICAL**: Security vulnerabilities, data loss risks, system-breaking bugs
  - **HIGH**: Blocking other work, critical bugs, foundational features
  - **MEDIUM**: Important features, non-critical bugs, enhancements
  - **LOW**: Nice-to-haves, optimizations, documentation

### Complexity (Optional)

- Indented with 2 spaces: `  - Complexity:`
- Valid values: `HIGH`, `MEDIUM`, `LOW`
- Guidelines:
  - **HIGH**: Large scope, many files, architectural changes, significant risk
  - **MEDIUM**: Moderate scope, several files, standard implementation
  - **LOW**: Small scope, few files, straightforward changes

### Dependencies (Required)

- Indented with 2 spaces: `  - Dependencies:`
- Format: Comma-separated task IDs or the word `none`
- Examples:
  - `none` - No dependencies
  - `TASK-001` - Single dependency
  - `TASK-001, TASK-002` - Multiple dependencies

### Scope (Optional)

- Indented with 2 spaces: `  - Scope:`
- Each item indented with 4 spaces: `    - Item description`
- Items become checklist items in the worker's PRD
- Use for breaking down larger tasks into specific deliverables

### Out of Scope (Optional)

- Indented with 2 spaces: `  - Out of Scope:`
- Each item indented with 4 spaces: `    - Item description`
- Helps prevent scope creep and clarify boundaries

### Acceptance Criteria (Optional)

- Indented with 2 spaces: `  - Acceptance Criteria:`
- Each item indented with 4 spaces: `    - Criterion description`
- Defines success criteria and validation points

## Instructions

When generating kanban tasks:

1. **Ask clarifying questions** if the user's description is vague:
   - What is the specific goal or outcome?
   - Are there any dependencies on other tasks?
   - What should be included/excluded from scope?
   - What priority level is appropriate?

2. **Determine the next task ID**:
   - Read the existing `.ralph/kanban.md` file
   - Find the highest task number
   - Increment by 1 for the new task
   - Use the same prefix pattern (typically `TASK-`)

3. **Generate task structure**:
   - Write a clear, imperative brief description
   - Provide detailed context in the Description field
   - Set appropriate priority (CRITICAL/HIGH/MEDIUM/LOW)
   - List dependencies or use "none"
   - Break complex tasks into Scope items
   - Define what's Out of Scope to prevent scope creep
   - Add Acceptance Criteria for validation

4. **Output the formatted task**:
   - Present the complete task entry
   - Ensure proper indentation (2 spaces for fields, 4 spaces for sub-items)
   - Verify all required fields are present
   - Ask if the user wants to add it to their kanban.md

## Examples

### Minimal Task

```markdown
- [ ] **[TASK-001]** Create README file
  - Description: Create a README.md with project description, installation instructions, and usage guide
  - Priority: HIGH
  - Dependencies: none
```

### Full-Featured Task

```markdown
- [ ] **[FEATURE-042]** Implement user authentication system
  - Description: Add JWT-based authentication with login, logout, and token refresh endpoints
  - Priority: HIGH
  - Complexity: HIGH
  - Dependencies: TASK-001, TASK-002
  - Scope:
    - Create authentication middleware
    - Implement login endpoint with JWT generation
    - Implement logout endpoint with token invalidation
    - Add token refresh mechanism
    - Create user session management
  - Out of Scope:
    - OAuth integration (future enhancement)
    - Two-factor authentication
    - Password reset functionality
  - Acceptance Criteria:
    - All endpoints return appropriate HTTP status codes
    - JWTs expire after configured timeout
    - Invalid tokens are rejected
    - Unit tests achieve 80% coverage
```

### Bug Fix Task

```markdown
- [ ] **[BUG-123]** Fix login form validation
  - Description: Login form allows empty passwords and doesn't show error messages properly
  - Priority: HIGH
  - Dependencies: none
  - Scope:
    - Add client-side validation for email and password
    - Display error messages below form fields
    - Prevent form submission when invalid
  - Acceptance Criteria:
    - Empty fields show validation errors
    - Invalid email format is rejected
    - Error messages are user-friendly
```

## Common Pitfalls

### Incorrect Indentation

**Wrong**:
```markdown
- [ ] **[TASK-001]** Do something
- Description: Details here
```

**Correct**:
```markdown
- [ ] **[TASK-001]** Do something
  - Description: Details here
```

### Missing Required Fields

**Wrong**:
```markdown
- [ ] **[TASK-001]** Do something
  - Description: Details here
```

**Correct**:
```markdown
- [ ] **[TASK-001]** Do something
  - Description: Details here
  - Priority: MEDIUM
  - Dependencies: none
```

### Invalid Task ID Format

**Wrong**:
```markdown
- [ ] **TASK-001** Do something        (missing brackets)
- [ ] **[T-1]** Do something           (prefix too short)
- [ ] **[VERYLONGPREFIX-001]** Do something  (prefix too long)
```

**Correct**:
```markdown
- [ ] **[TASK-001]** Do something
- [ ] **[FEAT-1]** Do something
- [ ] **[BUG-001]** Do something
```

### Incorrect Scope Indentation

**Wrong**:
```markdown
  - Scope:
  - First item
  - Second item
```

**Correct**:
```markdown
  - Scope:
    - First item
    - Second item
```

## Adding Tasks to Kanban

After generating a task:

1. Read the current `.ralph/kanban.md`
2. Find the `## TASKS` section
3. Add the new task entry at the end of the pending tasks
4. Maintain proper formatting and spacing
5. Save the file

Always verify the task ID is unique before adding.
