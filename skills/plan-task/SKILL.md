---
name: plan-task
description: Interactively plan task implementation
---

# Plan Task

Create implementation plans by exploring the codebase and designing an approach before coding.

## When to Use

- Before implementing a new feature or complex change
- When you need to understand existing patterns first
- To document architectural decisions before coding
- When breaking down a large task into steps

## Process

### 1. Understand Requirements

Ask clarifying questions:
- What is the specific goal or outcome?
- What constraints or requirements exist?
- Are there existing patterns to follow?
- What is out of scope?

### 2. Explore the Codebase (READ-ONLY)

Use these tools to understand the existing architecture:
- **Glob**: Find files by pattern (`**/*.ts`, `src/components/**`)
- **Grep**: Search for code patterns, function names, imports
- **Read**: Examine specific files in detail
- **Bash** (read-only only): `ls`, `git log`, `git diff`, `find`

Look for:
- Similar features as reference implementations
- Existing patterns and conventions
- Related code that will be affected
- Test patterns used in the project

### 3. Design the Solution

Consider:
- How does this fit the existing architecture?
- What are the trade-offs of different approaches?
- What dependencies exist between components?
- What could go wrong? Edge cases?

### 4. Document the Plan

Write a plan to `.ralph/plans/TASK-xxx.md` (or present to user) with this structure:

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
```

## Key Rules

1. **READ-ONLY during planning**: Do not create, modify, or delete files (except the plan itself)
2. **Be specific**: Reference actual file paths, function names, line numbers
3. **Follow existing patterns**: Find and document how similar things are done
4. **Critical Files required**: Always list 3-5 files most important to the implementation
5. **Consider edge cases**: Document potential challenges upfront

## Example Interaction

**User**: `/plan-task Add user authentication`

**Assistant**: I'll help you plan the authentication implementation. Let me explore the codebase first.

*[Explores with Glob, Grep, Read]*

Based on my exploration, I found:
- The project uses Express.js with TypeScript
- There's an existing middleware pattern in `src/middleware/`
- User model exists at `src/models/user.ts`
- Routes follow RESTful patterns in `src/routes/`

Let me ask a few questions:
1. What authentication method? (JWT, session-based, OAuth?)
2. Should it include registration, or just login?
3. Are there specific security requirements?

**User**: JWT with login and registration. Standard security.

**Assistant**: Here's the implementation plan:

```markdown
# Implementation Plan: AUTH-001

## Overview
Add JWT-based authentication with login and registration endpoints, following existing Express middleware patterns.

## Requirements Analysis
| Requirement | Acceptance Criteria | Complexity |
|-------------|---------------------|------------|
| User registration | POST /auth/register creates user, returns JWT | Medium |
| User login | POST /auth/login validates credentials, returns JWT | Medium |
| Protected routes | Middleware validates JWT, rejects invalid tokens | Medium |
| Password security | Passwords hashed with bcrypt, min 8 chars | Low |

## Existing Patterns
- `src/middleware/error-handler.ts`: Middleware pattern to follow
- `src/models/user.ts`: Existing user model structure
- `src/routes/users.ts`: Route organization pattern
- `src/utils/response.ts`: Standard response format

## Implementation Approach
1. **Add dependencies**: jsonwebtoken, bcrypt
2. **Extend User model**: Add password field, hash on save
3. **Create auth middleware**: Validate JWT, attach user to request
4. **Create auth routes**: /register, /login endpoints
5. **Add tests**: Unit tests for auth logic, integration for endpoints

## Dependencies and Sequencing
1. User model changes (no dependencies)
2. Auth middleware (depends on JWT secret config)
3. Auth routes (depends on model + middleware)
4. Tests (depends on all above)

## Potential Challenges
- JWT secret management (use environment variable)
- Token expiration handling
- Password validation rules consistency

### Critical Files
| Action | File | Reason |
|--------|------|--------|
| MODIFY | src/models/user.ts | Add password field and hashing |
| CREATE | src/middleware/auth.ts | JWT validation middleware |
| CREATE | src/routes/auth.ts | Login/register endpoints |
| MODIFY | src/app.ts | Register auth routes |
| REFERENCE | src/middleware/error-handler.ts | Middleware pattern |
```

Shall I save this to `.ralph/plans/AUTH-001.md` or proceed with implementation?

## Output Location

Plans are saved to: `.ralph/plans/[TASK-ID].md`

This allows:
- Review before implementation
- Reference during coding
- Documentation for future maintainers
- Input for Chief Wiggum workers
