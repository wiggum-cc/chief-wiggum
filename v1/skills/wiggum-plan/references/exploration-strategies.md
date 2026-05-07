# Exploration Strategies Reference

## Parallel Exploration Dimensions

Explore the codebase across four dimensions simultaneously to build comprehensive understanding.

### Dimension 0: Specifications & Contracts

**Goal:** Understand the authoritative specifications that govern the area this task touches.

**Strategy:**
1. Explore `spec/` — this is the source of truth. Do not assume internal structure; list what exists and read relevant files
2. Read `CLAUDE.md` or `AGENTS.md` at the project root for project-wide conventions
3. Explore `docs/` for analysis, research, references, and developer documentation
4. Identify which specs define the interfaces, schemas, or contracts affected by this task

**Search patterns:**
```bash
# Discover spec structure
Glob: "spec/**/*"

# Find project instructions
Glob: "{CLAUDE,AGENTS}.md"

# Explore documentation
Glob: "docs/**/*"

# Find schemas and contracts
Grep: "interface|schema|contract|protocol" in spec/
```

**What to document:**
- Which specs govern the area this task touches
- Whether current code aligns with or drifts from specs
- Which interfaces or contracts will need modification
- Whether the spec already accommodates the new requirements or needs extension

### Dimension A: Similar Features

**Goal:** Find existing features that solve similar problems.

**Strategy:**
1. Identify keywords from the task description
2. Search for those keywords in file names and content
3. Trace execution from entry points through the call chain
4. Document data transformations and state changes

**Search patterns:**
```bash
# Find similar feature files
Glob: "src/**/*{keyword}*"
Glob: "src/**/*{related-term}*"

# Find similar function implementations
Grep: "function.*{keyword}|const.*{keyword}"
Grep: "class.*{keyword}"

# Find similar API routes
Grep: "router\.(get|post|put|delete).*{path-segment}"
```

**What to document:**
- Entry points (routes, event handlers, CLI commands)
- Core logic location
- Data flow through the feature
- External dependencies used

### Dimension B: Architecture & Patterns

**Goal:** Understand how the codebase is organized and what conventions to follow.

**Strategy:**
1. Examine directory structure and naming conventions
2. Find configuration files that define patterns
3. Look for shared utilities and base classes
4. Identify abstraction layers

**Search patterns:**
```bash
# Find architectural patterns
Glob: "src/*/index.{ts,js}"
Glob: "src/{utils,helpers,lib,common}/**/*"

# Find base classes and interfaces
Grep: "abstract class|interface I|BaseController|BaseService"

# Find configuration
Glob: "**/config/**/*"
Glob: "**/*.config.{ts,js,json}"
```

**What to document:**
- Module boundaries
- Naming conventions (files, functions, variables)
- Error handling patterns
- Logging conventions
- Testing patterns

### Dimension C: Integration Points

**Goal:** Identify code that will interact with the new feature.

**Strategy:**
1. Find shared services and data models
2. Identify middleware and interceptors
3. Look for event systems and message buses
4. Understand database access patterns

**Search patterns:**
```bash
# Find shared models
Glob: "src/{models,entities,types}/**/*"

# Find shared services
Glob: "src/{services,providers}/**/*"

# Find middleware
Grep: "middleware|interceptor|guard"

# Find database access
Grep: "Repository|Model\.|prisma\.|knex\."
```

**What to document:**
- Services the feature will use
- Data models to interact with
- Events to emit or listen to
- APIs to call

### Dimension D: Interfaces & Coupling

**Goal:** Evaluate the interface surface between modules and identify opportunities to reduce coupling.

**Strategy:**
1. Map the current interface surface between modules this task touches
2. Identify shared state, configuration, or implicit contracts between modules
3. Assess whether modules have independent concerns (orthogonal) or hidden dependencies
4. Look for opportunities to narrow the interface rather than extend it

**Search patterns:**
```bash
# Find module boundaries
Glob: "src/*/index.{ts,js,sh}"
Glob: "lib/*/index.{ts,js,sh}"

# Find cross-module imports
Grep: "source|import|require" across module boundaries

# Find shared state or config
Grep: "global|shared|common" in relevant modules
```

**What to document:**
- Current interface contracts between affected modules (function signatures, file formats, schemas)
- Whether the interface surface can be reduced rather than extended
- Implicit contracts that should be made explicit
- Coupling points where a change in one module ripples into others
- Opportunities to make modules more orthogonal

## Key Files Identification

After exploration, identify 5-10 key files with specific insights.

**Key file categories:**
| Category | Example | What to Note |
|----------|---------|--------------|
| Specification | `spec/pipeline-schema.md` | Authoritative contract this task must conform to or extend |
| Pattern to follow | `src/routes/users.ts` | Route definition structure |
| Controller example | `src/controllers/userController.ts` | Error handling, response format |
| Service pattern | `src/services/emailService.ts` | Dependency injection, async patterns |
| Model reference | `src/models/User.ts` | Field types, relationships |
| Interface contract | `src/types/api.ts` | Module boundary definition |
| Test example | `tests/users.test.ts` | Test structure, mocking patterns |
| Config reference | `src/config/database.ts` | Configuration access pattern |
| Utility to reuse | `src/utils/validation.ts` | Shared utilities available |
| Middleware example | `src/middleware/auth.ts` | Middleware chain pattern |

## Exploration Depth Guidelines

**Surface level (quick scan):**
- File names and directory structure
- Function signatures and exports
- Import statements
- 1-2 minutes per file

**Medium depth (pattern extraction):**
- Function implementations
- Error handling approach
- Data transformations
- 3-5 minutes per file

**Deep dive (full understanding):**
- Complete execution flow tracing
- Edge case handling
- Performance considerations
- 10+ minutes per file

**When to go deeper:**
- File is a primary pattern to follow
- Logic is complex or non-obvious
- Integration is critical to the feature

## Iteration Guidelines

**When to iterate:**
- Found something that changes understanding
- User answer reveals new area to explore
- Initial findings are incomplete

**When to stop:**
- Have 5-10 key files identified
- Understand all four dimensions (specs, similar features, architecture, integration, interfaces)
- Know which specs are affected and whether they need modification
- Can answer: "How would existing code handle this?"
- Can answer: "Does this make the interface surface narrower or wider?"

## Anti-Patterns

### Premature Questions
```
# Bad - asking before exploring
"What pattern should we use?"

# Good - ask after finding options
"Found two patterns: X in src/a.ts and Y in src/b.ts. Which should we follow?"
```

### Surface Exploration
```
# Bad - only looking at file names
"Found auth.ts, probably handles authentication"

# Good - reading and understanding
"auth.ts:45-67 implements JWT validation using jsonwebtoken library"
```

### Missing Integration Points
```
# Bad - only looking at similar features
"Will create new route like users.ts"

# Good - understanding full context
"Will create route like users.ts, use existing errorHandler middleware,
and emit 'user.created' event for audit logging"
```
