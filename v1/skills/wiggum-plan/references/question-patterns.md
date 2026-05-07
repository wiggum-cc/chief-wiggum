# Question Patterns Reference

## Core Principles

1. **Ground in research** - Every option from actual findings
2. **Be specific** - No vague "Other approach" options
3. **Provide context** - Explain trade-offs in descriptions
4. **Stay focused** - One decision per question
5. **Enable choice** - 2-4 options per question

## AskUserQuestion Format

```
questions:
  - question: Clear question ending with ?
    header: Max12Chars
    multiSelect: false
    options:
      - label: 1-5 words
        description: Trade-offs and context
      - label: 1-5 words
        description: Trade-offs and context
```

## Question Categories

### Approach Selection
When multiple valid patterns exist:

```
questions:
  - question: Which data fetching pattern should we use?
    header: Data fetch
    multiSelect: false
    options:
      - label: React Query
        description: Found in src/hooks/, provides caching and refetching
      - label: SWR
        description: Lighter weight, used in dashboard components
      - label: Direct fetch
        description: Simpler, no caching, found in legacy code
```

### Scope Clarification
When requirements are ambiguous:

```
questions:
  - question: Should error handling include retry logic?
    header: Retry
    multiSelect: false
    options:
      - label: Yes, with backoff
        description: Exponential backoff like src/utils/api.ts
      - label: Yes, simple retry
        description: Fixed 3 retries, simpler implementation
      - label: No retry
        description: Fail fast, let caller handle
```

### Trade-off Decisions
When there's a clear trade-off:

```
questions:
  - question: Optimize for performance or simplicity?
    header: Optimize
    multiSelect: false
    options:
      - label: Performance
        description: Add caching layer, more complex but faster
      - label: Simplicity
        description: Direct queries, easier to maintain
```

### Feature Inclusion
When scope needs boundaries:

```
questions:
  - question: What password requirements?
    header: Password
    multiSelect: false
    options:
      - label: Minimum 8 chars
        description: Simple, good UX
      - label: Complex rules
        description: Upper, lower, number, special - more secure
      - label: Match existing
        description: Use rules from src/validation/password.ts
```

### Integration Points
When connecting to existing code:

```
questions:
  - question: Should this integrate with existing logging?
    header: Logging
    multiSelect: false
    options:
      - label: Use Winston logger
        description: Found in src/utils/logger.ts, structured logs
      - label: Console only
        description: Simpler, for dev environment
      - label: Both
        description: Winston in prod, console in dev
```

## Question Count Guidelines

**1-2 questions**: Simple clarification
- Single ambiguous point
- Binary choice

**3-4 questions**: Moderate complexity
- Multiple independent decisions
- Feature with options

**5-6 questions**: Complex scenario
- Major feature
- Architectural decisions
- Multiple trade-offs

## Anti-Patterns

### Too Vague
```
# Bad
options:
  - label: Option A
    description: One way to do it
  - label: Option B
    description: Another way

# Good
options:
  - label: JWT tokens
    description: Stateless, found in src/auth/
  - label: Session cookies
    description: Stateful, requires Redis
```

### Not Grounded
```
# Bad - no evidence from codebase
options:
  - label: Use Redux
    description: Popular state management

# Good - grounded in findings
options:
  - label: Use Redux
    description: Already configured in src/store/
```

### Compound Questions
```
# Bad - multiple decisions in one
question: What auth method and where to store tokens?

# Good - separate questions
question: What authentication method?
question: Where should tokens be stored?
```
