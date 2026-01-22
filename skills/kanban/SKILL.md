---
name: kanban
description: Generate Kanban task entries with dependency analysis
---

# Kanban Task Generator

Generate properly formatted task entries for Chief Wiggum's `.ralph/kanban.md` file. This skill analyzes existing tasks and dependencies to create well-structured, interlinked task sets.

## Critical Rules

1. **ALWAYS read the entire kanban first** - Analyze existing tasks and dependencies before generating new ones
2. **Output multiple tasks when appropriate** - Break large features into reasonably-sized, interlinked tasks
3. **Dependencies are critical** - Carefully analyze and set dependencies based on execution order
4. **Reasonable task size** - Each task should be completable by a single worker in one session

## Process

### 1. Analyze Existing Kanban

First, read `.ralph/kanban.md` and analyze:
- What tasks already exist?
- What's the highest task number? (for ID assignment)
- What dependencies exist between tasks?
- Are there incomplete tasks the new work depends on?
- What prefix pattern is used? (TASK-, FEATURE-, etc.)

### 2. Understand the Request

Ask clarifying questions if needed:
- What is the specific goal or outcome?
- Should this be one task or multiple?
- What existing tasks does this depend on?
- What priority level is appropriate?

### 3. Design Task Structure

For complex features, break into multiple tasks:
- Each task should be **reasonably sized** (1 worker, 1 session)
- Set **dependencies** so tasks execute in correct order
- Tasks without dependencies can run in parallel
- Use Scope to break down individual tasks further

### 4. Generate and Add Tasks

- Present all tasks to the user
- Confirm before adding to kanban
- Add to the `## TASKS` section
- Verify all IDs are unique

## Task Entry Format

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
- **Pattern**: `[A-Za-z]{2,8}-[0-9]+`
- **Examples**: `[TASK-001]`, `[FEATURE-042]`, `[BUG-123]`
- Must be unique across the kanban file

### Status Checkbox
| Marker | Status | Description |
|--------|--------|-------------|
| `- [ ]` | Pending | Not started |
| `- [=]` | In-progress | Worker actively processing |
| `- [P]` | Pending Approval | PR created, awaiting merge |
| `- [x]` | Complete | PR merged |
| `- [N]` | Not Planned | Won't be done |
| `- [*]` | Failed | Worker encountered errors |

**Dependency Resolution**: Only `[x]` (Complete) satisfies dependencies. `[P]` (Pending Approval) does NOT.

### Priority
- **CRITICAL**: Security vulnerabilities, data loss risks, system-breaking bugs
- **HIGH**: Blocking other work, critical bugs, foundational features
- **MEDIUM**: Important features, non-critical bugs, enhancements
- **LOW**: Nice-to-haves, optimizations, documentation

### Dependencies
- Format: Comma-separated task IDs or `none`
- Only reference tasks that exist in the kanban
- Consider both technical and logical dependencies

## Example Interaction

**User**: `/kanban Add user authentication with JWT`

**Assistant**: I'll help create kanban tasks for JWT authentication. Let me first analyze the existing kanban.

*[Reads .ralph/kanban.md]*

I found:
- 12 existing tasks (TASK-001 through TASK-012)
- TASK-008 (User model) is complete `[x]`
- TASK-010 (API routing setup) is pending approval `[P]`
- TASK-011 (Error handling middleware) is in progress `[=]`

A few questions:
1. Should this include registration, or just login?
2. Do you need password reset functionality?
3. What priority - is this blocking other work?

**User**: Login and registration, no password reset. High priority, it's blocking the dashboard work.

**Assistant**: Based on the existing kanban, I'll create 3 interlinked tasks. Note that TASK-010 (API routing) is still pending approval, so I'll set that as a dependency since auth routes need the router setup.

Here are the tasks:

```markdown
- [ ] **[TASK-013]** Create JWT authentication utilities
  - Description: Create JWT token generation, validation, and refresh utilities following existing patterns in src/utils/
  - Priority: HIGH
  - Complexity: MEDIUM
  - Dependencies: TASK-008
  - Scope:
    - Create src/utils/jwt.ts with sign/verify functions
    - Add JWT secret to environment config
    - Create token refresh logic
  - Acceptance Criteria:
    - Tokens expire after configured timeout
    - Invalid tokens throw appropriate errors

- [ ] **[TASK-014]** Create authentication middleware
  - Description: Create Express middleware to validate JWT tokens on protected routes
  - Priority: HIGH
  - Complexity: LOW
  - Dependencies: TASK-013, TASK-011
  - Scope:
    - Create src/middleware/auth.ts
    - Extract and validate JWT from Authorization header
    - Attach user to request object
  - Acceptance Criteria:
    - Invalid tokens return 401
    - Missing tokens return 401
    - Valid tokens attach user to req.user

- [ ] **[TASK-015]** Create auth routes (login/register)
  - Description: Create POST /auth/login and POST /auth/register endpoints
  - Priority: HIGH
  - Complexity: MEDIUM
  - Dependencies: TASK-013, TASK-014, TASK-010
  - Scope:
    - Create src/routes/auth.ts
    - Implement login with password validation
    - Implement registration with input validation
    - Hash passwords with bcrypt
  - Out of Scope:
    - Password reset
    - OAuth integration
  - Acceptance Criteria:
    - Registration creates user and returns JWT
    - Login validates credentials and returns JWT
    - Invalid credentials return 401
```

**Dependency graph:**
```
TASK-008 (User model) [x]
    └── TASK-013 (JWT utils)
            └── TASK-014 (Auth middleware)
            │       └── TASK-015 (Auth routes)
            └───────────┘
TASK-011 (Error handling) [=]
    └── TASK-014

TASK-010 (API routing) [P]
    └── TASK-015
```

Note: TASK-015 won't start until TASK-010's PR is merged (dependencies require `[x]` status).

Shall I add these to `.ralph/kanban.md`?

**User**: Yes, add them.

**Assistant**: *[Adds tasks to .ralph/kanban.md]*

Added 3 tasks to the kanban:
- TASK-013: JWT utilities (can start immediately, depends on completed TASK-008)
- TASK-014: Auth middleware (waits for TASK-013 and TASK-011)
- TASK-015: Auth routes (waits for TASK-013, TASK-014, and TASK-010 to be merged)

The dependency chain ensures correct execution order. TASK-013 can be picked up by a worker now.

## Task Sizing Guidelines

**Too large** (split into multiple tasks):
- "Implement entire authentication system"
- "Build user dashboard with all features"
- "Refactor the entire codebase"

**Right size** (single task):
- "Create JWT token utilities"
- "Add login endpoint"
- "Create auth middleware"
- "Add password validation to user model"

**Too small** (combine or use Scope items):
- "Add import statement"
- "Create empty file"
- "Add single function parameter"
