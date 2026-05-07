# Task Sizing Guidelines

## Right-Sized Tasks

A well-sized task should be:
- Completable by **one worker in one session**
- Focused on a **single concern**
- **Testable** independently
- Clear **start and end** points

## Size Examples

### Too Large (Split These)

❌ "Implement entire authentication system"
- Should be: JWT utils, middleware, routes, tests (4 tasks)

❌ "Build user dashboard with all features"
- Should be: Layout, profile panel, activity feed, settings (4 tasks)

❌ "Refactor the entire codebase"
- Should be: Identify specific modules, create task per module

❌ "Add comprehensive test coverage"
- Should be: Task per module or feature area

### Right Size (Good Tasks)

✅ "Create JWT token utilities"
- Single file, clear scope, testable

✅ "Add login endpoint"
- One route, one controller, one test file

✅ "Create auth middleware"
- Single middleware file with tests

✅ "Add password validation to user model"
- One model change, one test update

### Too Small (Combine These)

❌ "Add import statement"
- Combine with the feature that needs it

❌ "Create empty file"
- Combine with populating that file

❌ "Add single function parameter"
- Combine with the feature using that parameter

❌ "Fix typo in variable name"
- Combine with related work or skip if trivial

## Sizing Heuristics

### File Count
- **1-3 files**: Single task
- **4-6 files**: Consider splitting
- **7+ files**: Definitely split

### Scope Items
- **1-3 items**: Single task
- **4-5 items**: Review if items are related
- **6+ items**: Split into multiple tasks

### Estimated Lines Changed
- **< 200 lines**: Single task
- **200-500 lines**: Review scope
- **500+ lines**: Split

### Dependencies Created
- If a task would create **3+ new dependencies**, it's too large
- Split so each task creates **1-2 dependencies**

## Splitting Strategies

### By Layer
```
Original: "Add user profile feature"

Split:
- TASK-001: Create user profile database schema
- TASK-002: Create user profile API endpoints
- TASK-003: Create user profile UI components
```

### By Function
```
Original: "Implement authentication"

Split:
- TASK-001: JWT token generation/validation
- TASK-002: Auth middleware
- TASK-003: Login endpoint
- TASK-004: Registration endpoint
```

### By Phase
```
Original: "Migrate database to new schema"

Split:
- TASK-001: Create migration scripts
- TASK-002: Add backward compatibility layer
- TASK-003: Migrate existing data
- TASK-004: Remove compatibility layer
```

## Using Scope for Breakdown

When a task is right-sized but complex, use Scope items:

```markdown
- [ ] **[TASK-015]** Create auth routes
  - Description: Login and registration endpoints
  - Priority: HIGH
  - Dependencies: TASK-013, TASK-014
  - Scope:
    - Create route file structure
    - Implement POST /auth/login
    - Implement POST /auth/register
    - Add input validation
    - Add error handling
    - Write tests
```

Scope items become the worker's checklist without creating separate tasks.
