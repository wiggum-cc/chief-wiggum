---
name: wiggum-plan
description: Interactively plan task implementation (planning only, no implementation)
---

# Wiggum Plan

Create implementation plans by exploring the codebase and designing an approach. This skill is for **planning only** - it never implements.

## Input

A task ID from `.ralph/kanban.md` (e.g., `TASK-015`, `FEATURE-042`).

## Critical Rules

1. **NEVER implement** - This skill produces plans, not code
2. **ALWAYS write the plan file** - Every session must end with writing `.ralph/plans/TASK-ID.md`
3. **Multiple iterations allowed** - Explore, ask questions, explore more as needed
4. **READ-ONLY exploration** - Only modify the plan file itself

## Process

### 1. Explore and Understand (iterative)

This phase may repeat multiple times until you have a complete picture.

**Read the task requirements:**
- Read `.ralph/kanban.md` and find the task entry for the given ID
- Extract Description, Scope, Acceptance Criteria, Dependencies

**Explore the codebase (READ-ONLY):**
- **Glob**: Find files by pattern (`**/*.ts`, `src/components/**`)
- **Grep**: Search for code patterns, function names, imports
- **Read**: Examine specific files in detail
- **Bash** (read-only only): `ls`, `git log`, `git diff`, `find`

Look for:
- Similar features as reference implementations
- Existing patterns and conventions
- Related code that will be affected
- Test patterns used in the project

**Ask clarifying questions:**
- What constraints or requirements aren't clear?
- Are there ambiguities in the task description?
- What trade-offs should be considered?

**Iterate:** After getting answers, explore more if needed. Repeat until you have a complete understanding.

### 2. Design the Solution

Consider:
- How does this fit the existing architecture?
- What are the trade-offs of different approaches?
- What dependencies exist between components?
- What could go wrong? Edge cases?
- How does the solution impact other in progress and new tasks?

### 3. Write the Plan (REQUIRED)

**You MUST write the plan to `.ralph/plans/TASK-ID.md`** - this is not optional.

Use this structure:

```markdown
# Implementation Plan: [TASK-ID]

## Overview
[1-2 sentences: what will be implemented and why]

## Requirements Analysis
| Requirement | Acceptance Criteria | Complexity |
|-------------|---------------------|------------|
| [requirement] | [how to verify] | Low/Med/High |

## Existing Patterns
[Patterns found in codebase that implementation should follow]
- `path/to/file.ts`: [pattern description]
- `path/to/other.ts`: [pattern description]

## Implementation Approach
[Step-by-step strategy with specific file/function references]

1. **Step 1**: [what to do]
   - File: `path/to/file`
   - Changes: [specific changes]

2. **Step 2**: [what to do]
   - File: `path/to/file`
   - Changes: [specific changes]

## Dependencies and Sequencing
[Order of operations, what depends on what]

## Potential Challenges
[Technical risks, edge cases, things to watch out for]

### Critical Files
| Action | File | Reason |
|--------|------|--------|
| CREATE | path/file.ext | [Purpose] |
| MODIFY | path/file.ext | [What changes] |
| REFERENCE | path/file.ext | [Pattern to follow] |

### Incompatible With (only if applicable)
TASK-029
```

## Example Interaction

**User**: `/wiggum-plan TASK-015`

**Assistant**: I'll create an implementation plan for TASK-015. Let me read the task requirements first.

*[Reads .ralph/kanban.md]*

Found TASK-015:
```
- [ ] **[TASK-015]** Create auth routes (login/register)
  - Description: Create POST /auth/login and POST /auth/register endpoints
  - Priority: HIGH
  - Dependencies: TASK-013, TASK-014, TASK-010
  - Scope:
    - Create src/routes/auth.ts
    - Implement login with password validation
    - Implement registration with input validation
    - Hash passwords with bcrypt
  - Out of Scope:
    - Password reset
    - OAuth integration
```

Now let me explore the codebase to understand existing patterns...

*[Uses Glob to find route files]*

*[Uses Read to examine src/routes/users.ts]*

I see the route pattern. Let me check the dependencies...

*[Reads TASK-013 and TASK-014 entries to understand what they provide]*

I have some questions:
1. Should registration require email verification, or is immediate access OK?
2. What validation rules for passwords? (min length, complexity?)
3. Should failed login attempts be rate-limited?

**User**: No email verification. Min 8 chars for password. Yes, rate limit to 5 attempts per minute.

**Assistant**: Good to know about rate limiting - let me check if there's an existing rate limiter...

*[Uses Grep to search for rate limiting patterns]*

Found `src/middleware/rate-limit.ts`. I'll reference that pattern.

Now I have a complete picture. Writing the plan. Note that this design is incompatible with TASK-029.

*[Writes to .ralph/plans/TASK-015.md]*

I've saved the implementation plan to `.ralph/plans/TASK-015.md`. The plan covers:

- Route structure following existing patterns in `src/routes/users.ts`
- Integration with JWT utils from TASK-013
- Integration with auth middleware from TASK-014
- Rate limiting using existing `src/middleware/rate-limit.ts` pattern
- Password validation (min 8 chars)
- Bcrypt hashing

The plan is ready for a Chief Wiggum worker to execute. Shall I mark TASK-029 as [N] Not planned?

## Output

Plans are saved to: `.ralph/plans/[TASK-ID].md`

This allows:
- Review before implementation
- Reference during coding
- Documentation for future maintainers
- Input for Chief Wiggum workers
