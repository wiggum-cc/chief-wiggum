| name | description |
|------|-------------|
| kanban | Generate properly formatted kanban task entries with dependency analysis. Analyzes existing tasks, breaks features into reasonably-sized items, and ensures correct dependency chains. |

# Kanban Task Generator

## Purpose

Generate properly formatted task entries for Chief Wiggum's `.ralph/kanban.md` file. This skill analyzes existing tasks and dependencies to create well-structured, interlinked task sets.

## When This Skill is Invoked

**Manual invocation:**
- User wants to add new tasks to the kanban
- User has a feature idea that needs to be broken into tasks
- User has completed `/wiggum-ideas` and wants to formalize selected ideas

**From other skills:**
- After `/wiggum-plan` identifies work items
- After `/wiggum-ideas` generates approved ideas

## Core Workflow

### Phase 1: Analyze Existing Kanban

Read `.ralph/kanban.md` and gather context:
- What tasks already exist?
- What's the highest task number? (for ID assignment)
- What dependencies exist between tasks?
- What tasks are in progress `[=]` or pending approval `[P]`?
- What prefix pattern is used? (TASK-, FEATURE-, etc.)

**Critical:** Never skip this phase. Dependencies must reference real tasks.

### Phase 2: Clarify Requirements

Use AskUserQuestion to gather missing information based on findings.

**AskUserQuestion Format:**
```
- question: Clear, specific question ending with ?
- header: Short label (max 12 chars)
- multiSelect: false (unless choices aren't mutually exclusive)
- options: 2-4 specific choices grounded in kanban analysis
  - label: Concise choice text (1-5 words)
  - description: Context about trade-offs or implications
```

**Question types:**
- **Scope**: Should this be one task or multiple?
- **Dependencies**: Does this depend on existing tasks?
- **Priority**: Is this blocking other work?
- **Sizing**: How should we break this down?

### Phase 3: Design Task Structure

For complex features, break into multiple tasks:
- Each task should be **reasonably sized** (1 worker, 1 session)
- Set **dependencies** so tasks execute in correct order
- Tasks without dependencies can run in parallel
- Use Scope field to break down individual tasks further

### Phase 4: Present and Add Tasks

- Present all tasks with dependency graph
- Use AskUserQuestion to confirm before adding
- Add to the `## TASKS` section of `.ralph/kanban.md`
- Verify all IDs are unique

For task format specifications, see references/task-format.md.
For dependency patterns, see references/dependency-patterns.md.

## Example

**User**: `/kanban Add user authentication with JWT`

**Assistant**: I'll analyze the existing kanban first.

*[Reads .ralph/kanban.md]*

Found 12 tasks. TASK-008 (User model) is complete, TASK-010 (API routing) is pending approval `[P]`.

*[Uses AskUserQuestion]*
```
questions:
  - question: What authentication features should be included?
    header: Auth scope
    multiSelect: true
    options:
      - label: Login endpoint
        description: POST /auth/login with credential validation
      - label: Registration endpoint
        description: POST /auth/register with input validation
      - label: Password reset
        description: Forgot password flow with email verification
      - label: Token refresh
        description: Refresh expired tokens without re-login
```

**User selects**: Login endpoint, Registration endpoint, Token refresh

**Assistant**:
*[Uses AskUserQuestion]*
```
questions:
  - question: What priority level for these tasks?
    header: Priority
    multiSelect: false
    options:
      - label: CRITICAL
        description: Blocking all other work, needs immediate attention
      - label: HIGH
        description: Important, blocking dashboard work
      - label: MEDIUM
        description: Important but not blocking other tasks
```

**User selects**: HIGH

**Assistant**: Based on analysis, I'll create 3 interlinked tasks. Note TASK-010 is `[P]` so won't satisfy dependencies until merged.

```markdown
- [ ] **[TASK-013]** Create JWT authentication utilities
  - Description: Create JWT token generation and validation utilities
  - Priority: HIGH
  - Complexity: MEDIUM
  - Dependencies: TASK-008

- [ ] **[TASK-014]** Create authentication middleware
  - Description: Create Express middleware to validate JWT tokens
  - Priority: HIGH
  - Complexity: LOW
  - Dependencies: TASK-013

- [ ] **[TASK-015]** Create auth routes (login/register)
  - Description: Create login and registration endpoints with token refresh
  - Priority: HIGH
  - Complexity: MEDIUM
  - Dependencies: TASK-013, TASK-014, TASK-010
```

**Dependency graph:**
```
TASK-008 [x] ─── TASK-013 ─┬─ TASK-014 ─┬─ TASK-015
                           └────────────┘
TASK-010 [P] ─────────────────────────────┘
```

*[Uses AskUserQuestion]*
```
questions:
  - question: Add these tasks to .ralph/kanban.md?
    header: Confirm
    multiSelect: false
    options:
      - label: Yes, add all
        description: Add all 3 tasks to kanban
      - label: Modify first
        description: I want to change something before adding
```

## Key Principles

1. **Always analyze first** - Read kanban before generating tasks
2. **Ground in findings** - Dependencies must reference real tasks
3. **Reasonable sizing** - Each task completable in one worker session
4. **Explicit dependencies** - Show dependency graph for clarity
5. **Confirm before writing** - Always ask before modifying kanban

## Progressive Disclosure

This SKILL.md contains the core workflow. For detailed guidance:
- **Task format**: references/task-format.md
- **Dependency patterns**: references/dependency-patterns.md
- **Sizing guidelines**: references/sizing-guidelines.md
