| name | description |
|------|-------------|
| wiggum-plan | Create implementation plans through systematic multi-phase workflow: discovery, exploration, clarifying questions, architecture design, plan writing, kanban entry, and summary. Planning only - NEVER implements. Always writes plan to `.ralph/plans/TASK-ID.md` before adding task to kanban. |

# Wiggum Plan

## Purpose

Create implementation plans through a systematic 7-phase workflow that ensures deep codebase understanding and thoughtful architecture decisions. This skill is for **planning only** - it NEVER implements code.

**CRITICAL**: This skill produces `.ralph/plans/TASK-ID.md` files. It does NOT implement anything. Every invocation must result in a written plan file (or a list of unplanned tasks in Mode 3).

## Input

**Mode 1 - Existing Task**: A task ID from `.ralph/kanban.md` (e.g., `TASK-015`, `FEATURE-042`).

**Mode 2 - New Task**: A description of work to be done (e.g., "Add user authentication with JWT"). When no valid task ID is provided, the skill will:
1. Design the task and determine the task ID
2. Create the implementation plan in `.ralph/plans/TASK-ID.md`
3. Add the task to `.ralph/kanban.md`

**Mode 3 - No Argument (Audit Mode)**: When invoked with no argument, the skill will:
1. Read `.ralph/kanban.md` to find all pending/in-progress tasks
2. Check `.ralph/plans/` to identify which tasks already have plans
3. List all tasks that do NOT have a plan file
4. Group unplanned tasks into logical clusters based on:
   - Shared dependencies (tasks depending on or blocked by the same tasks)
   - Related functionality (similar descriptions, overlapping scope)
   - Sequential work (tasks that would naturally be planned together)
5. Present the grouped list to the user with suggestions for which groups to plan next
6. **Do NOT automatically create plans** - let the user choose which task(s) to plan

## When This Skill is Invoked

**Manual invocation:**
- `/wiggum-plan TASK-ID` - Plan a specific existing task
- `/wiggum-plan "description"` - Design and plan a new task
- `/wiggum-plan` (no argument) - Audit: list all tasks without plans, grouped logically

**Use cases:**
- Before implementing a complex task
- When a task needs architectural analysis
- To document approach before handing to a worker
- To see what tasks still need planning (audit mode)
- To identify which tasks should be planned together

**From other skills:**
- After `/kanban` creates tasks that need detailed planning

## Critical Rules

1. **NEVER implement** - This skill produces plans, not code. Do NOT write, edit, or create any code files. Do NOT run implementation commands. Your ONLY output is the plan file.
2. **NEVER enter plan mode** - Do NOT use the `EnterPlanMode` tool. This skill IS the planning mechanism. You explore, research, ask questions, and write the plan file directly. Claude Code's built-in plan mode is redundant and would create confusion.
3. **ALWAYS write the plan file** - Every session (except Mode 3 audit) MUST end with writing `.ralph/plans/TASK-ID.md`. The plan file is your deliverable. If you don't write the plan file, the session failed.
3. **Check existing task IDs first** - Before creating any plan, read `.ralph/kanban.md` to understand:
   - Which task IDs already exist (avoid duplicates/conflicts)
   - The highest task number (for ID assignment if creating new tasks)
   - Task prefixes used in this project
4. **Check related tasks** - Before planning, read descriptions AND existing plans of:
   - Tasks this one depends on (what do they provide?)
   - Tasks that depend on this one (what do they expect?)
   - Tasks with similar scope or overlapping functionality
   - Any task referenced in the Description or Scope
5. **Multiple iterations allowed** - Explore, ask questions, explore more as needed
6. **READ-ONLY exploration** - Only modify the kanban file (when creating tasks) and plan file
7. **Create task when needed** - If no valid task ID is provided, design the task and determine the ID first, but write the kanban entry only after the plan is written
8. **Clarifying questions are critical** - Never skip Phase 3; it's one of the most important phases

## Mode 3: Audit Workflow (No Argument)

When invoked without any argument, execute this audit workflow instead of the planning phases:

### Step 1: Scan Kanban
- Read `.ralph/kanban.md` completely
- Extract all tasks with status `[ ]` (Pending) or `[=]` (In-progress)
- Note their IDs, descriptions, priorities, and dependencies

### Step 2: Check for Existing Plans
- List all files in `.ralph/plans/`
- For each pending/in-progress task, check if `.ralph/plans/TASK-ID.md` exists
- Create two lists: tasks WITH plans, tasks WITHOUT plans

### Step 3: Group Unplanned Tasks
Group tasks WITHOUT plans into logical clusters:

**Grouping criteria (in order of priority):**
1. **Dependency chains**: Tasks that depend on each other or share common dependencies
2. **Functional area**: Tasks touching the same module, feature, or subsystem
3. **Scope overlap**: Tasks with similar descriptions or complementary functionality
4. **Sequential candidates**: Tasks that would naturally flow from one to the next

### Step 4: Present Findings
Output a structured report:

```markdown
## Unplanned Tasks Audit

### Tasks WITH Plans (ready for execution)
- [TASK-ID] Description... → `.ralph/plans/TASK-ID.md`

### Tasks WITHOUT Plans

#### Group 1: [Group Name - e.g., "Rate Limiting & Circuit Breaker"]
**Why grouped**: [Shared dependency on X, both touch Y module]
**Suggested planning order**: TASK-A → TASK-B
- [ ] **[TASK-A]** Description...
  - Priority: X | Dependencies: Y
- [ ] **[TASK-B]** Description...
  - Priority: X | Dependencies: TASK-A

#### Group 2: [Group Name]
...

### Standalone Tasks (no clear grouping)
- [ ] **[TASK-X]** Description...

### Recommended Next Steps
1. Plan [Group 1] first because [reason]
2. Consider planning [TASK-X] and [TASK-Y] together because [reason]
```

### Step 5: Await User Selection
- Do NOT automatically start planning
- Let the user choose which task or group to plan
- If user selects a task, transition to the normal planning workflow (Phase 0 or Phase 1)

---

## Core Workflow: 7 Phases

### Phase 0: Task Design (when no task ID provided)

**Skip this phase if a valid task ID was provided.**

When the input is a description rather than a task ID:

**Analyze existing kanban (REQUIRED):**
- Read `.ralph/kanban.md` completely
- Identify the highest task number for ID assignment (e.g., if TASK-036 exists, next is TASK-037)
- Note task prefixes used in this project (TASK-, FEAT-, BUG-, etc.)
- Check for similar/related pending tasks — these may need to be planned together or sequenced

**Check existing plans for related tasks:**
- List all files in `.ralph/plans/`
- For tasks with similar scope, read their existing plans
- Note patterns, decisions, and architectural context from related plans
- Identify if this new task conflicts with or complements existing plans

**Clarify requirements with AskUserQuestion:**
- Scope: What should be included/excluded?
- Priority: How urgent is this work?
- Dependencies: Does this depend on existing tasks?

**Design the task:**
- Determine if it should be one task or multiple
- If multiple tasks needed, break down with proper dependencies (use Scope field for sub-items within a single task)
- Each task should be completable by one worker in one session
- Assign the task ID(s) now — you need them for plan file paths

**Do NOT write to kanban yet.** The kanban entry is written after the plan (Phase 5.5). Hold the task details (ID, description, priority, dependencies, scope) in memory and carry them through the planning phases.

For task format details, see `/kanban` skill references:
- Task format: `skills/kanban/references/task-format.md`
- Dependency patterns: `skills/kanban/references/dependency-patterns.md`
- Sizing guidelines: `skills/kanban/references/sizing-guidelines.md`

**After task design, continue to Phase 1 with the determined task ID.**

---

### Phase 1: Research

**Goal:** Deep understanding of the requirements, the system, and the specifications before touching any code. This is NOT just reading the task — it is understanding how the system works and how the new requirements fit within it.

**Read the task requirements:**
- For existing tasks: Read `.ralph/kanban.md` and find the task entry for the given ID
- For new tasks (from Phase 0): Use the task details held in memory from the design phase
- Extract Description, Scope, Acceptance Criteria, Dependencies
- Classify the task: is this a bug fix, a new feature, a refactor, or a behavioral change?

**Read related tasks and their plans (REQUIRED):**
- For each task in the Dependencies field: read its kanban entry AND check if `.ralph/plans/TASK-ID.md` exists
- If a dependency has a plan, read it — understand what that task provides, its architectural decisions, interface changes
- Search kanban for tasks that depend on THIS task — read their entries to understand what they expect
- Search for tasks with overlapping scope or similar descriptions
- Check `.ralph/plans/` for any related plans that might inform this work
- Document: What context do related tasks provide? What constraints do they impose?

**Read project-level instructions:**
- Read `CLAUDE.md` or `AGENTS.md` at the project root (if they exist) for conventions and constraints
- Explore `docs/` for analysis, research, references, and developer documentation

**Discover and read specifications:**
- Explore `spec/` — this is the source of truth for specifications. Do not assume any internal structure; list what you find and read each spec relevant to the task
- Determine how the new requirements fit within the existing specifications
- Identify which interfaces, contracts, or schemas are affected
- Does the spec already accommodate this requirement, or does it need to be extended?
- Flag any cases where current code already deviates from spec — the plan should correct drift, not entrench it

**Ask initial clarifying questions:**
- What problem does this solve?
- What is the desired functionality?
- Are there any constraints or requirements not in the task?
- What does success look like?

**Output:** Clear understanding of requirements, specifications, and constraints before diving into code.

---

### Phase 2: Codebase Exploration (Parallel Analysis)

**Goal:** Build comprehensive understanding of relevant existing code through parallel exploration of four dimensions.

**Dimension A - Similar Features:**
- Search for existing features that solve similar problems
- Trace execution paths from entry points through data transformations
- Document how existing features are structured
- **For bug fixes**: Trace the failure path, identify root cause (not just symptoms), find sibling bugs sharing the same cause, check why existing tests missed it
- **For new features**: Map every component the feature will touch, find analogous features as implementation references

**Dimension B - Architecture & Patterns:**
- Map abstraction layers and module boundaries
- Identify design patterns used in the codebase
- Understand technology stack and conventions
- Study how the system works end-to-end for the area this task touches
- Understand existing abstractions — what they encapsulate and what assumptions they encode

**Dimension C - Integration Points:**
- Find code that will interact with the new feature
- Identify shared utilities, services, and data models
- Understand testing patterns and coverage expectations

**Dimension D - Interfaces & Coupling:**
- What is the current interface surface between the modules this task touches?
- Can the integration surface be *reduced* rather than extended? Fewer touch-points is better
- Are the affected modules orthogonal — independent concerns, or hidden coupling?
- If modules share state, configuration, or implicit contracts, can these be made explicit and narrow?
- Would an explicit interface (function contract, file format, schema) make two modules less entangled?
- Prefer designs where a change in one module does not ripple into unrelated modules

**Exploration tools (READ-ONLY):**
- **Glob**: Find files by pattern
- **Grep**: Search for code patterns, function names, imports
- **Read**: Examine specific files in detail
- **Bash** (read-only): `ls`, `git log`, `git diff`

**Output:** Identify key files for reference with specific insights from each. Catalog every file that will need to change, with specific line ranges.

---

### Phase 3: Clarifying Questions (CRITICAL)

**Goal:** Address all remaining ambiguities before designing architecture.

> ⚠️ **This is one of the most important phases. Do not skip it.**

**Consolidate questions from exploration into categories (ask in this order):**

1. **Architectural Direction** *(always first)*: Present any architectural improvements the new requirements make possible — consolidation, decoupling, simplification. Ground options in Phase 1-2 findings. If no changes are warranted, state why.
2. **Integration Points**: How should this interact with existing systems?
3. **Design Preferences**: Performance vs simplicity? Explicit vs convention?
4. **Edge Cases & Error Handling**: Failure modes, empty states, retry logic
5. **Scope Boundaries**: What's explicitly out of scope?

**AskUserQuestion Format:**
```yaml
questions:
  - question: Should we consolidate modules X and Y behind a shared interface?
    header: Architecture
    multiSelect: false
    options:
      - label: Consolidate (Recommended)
        description: "Reduces coupling. X (src/x.sh:40) and Y (src/y.sh:15) share 3 implicit contracts"
      - label: Keep separate
        description: "Lower risk, but interface surface stays wide"
```

**Guidelines:**
- Ground every option in codebase findings (cite file paths)
- One decision per question (avoid compound questions)
- Provide trade-off context in descriptions
- Ask 3-6 questions for complex features

**Output:** All ambiguities resolved with clear decisions documented.

---

### Phase 4: Architecture Design (Multiple Approaches)

**Goal:** Present 2-3 architecture approaches with trade-off analysis, then recommend the best fit.

**Reflect on best practices first:**
- How is this kind of problem solved in well-tested production systems?
- What are established patterns in the broader ecosystem for this functionality?
- Are there known pitfalls, anti-patterns, or scaling concerns with the naive approach?
- What would a senior architect critique about the simplest possible implementation?

**Generate approaches:**

| Approach | Description | When to Use |
|----------|-------------|-------------|
| **Minimal Changes** | Smallest possible footprint, follows existing patterns exactly | Time-critical, low-risk features |
| **Clean Architecture** | Ideal design with proper abstractions and separation | Foundational features, long-term maintainability |
| **Pragmatic Balance** | Balanced trade-off between minimal and clean | Most features; good default |

**For each approach, document:**
- Key architectural decisions and rationale
- Component design with file paths and responsibilities
- Data flow from entry points through transformations
- Files to CREATE vs MODIFY vs REFERENCE
- Specification impact: which specs need modification, interface surface changes (narrower/same/wider)
- Whether modules can be consolidated or simplified, or whether new abstractions are justified
- Pros and cons

**Present trade-off analysis:**
```
questions:
  - question: Which architecture approach should we use?
    header: Approach
    multiSelect: false
    options:
      - label: Minimal Changes (Recommended)
        description: "Add to existing X pattern in src/Y. Fast, low risk. Trade-off: less flexible"
      - label: Clean Architecture
        description: "New abstraction layer with proper interfaces. Trade-off: more files, higher effort"
      - label: Pragmatic Balance
        description: "Extend existing patterns with targeted improvements. Trade-off: moderate complexity"
```

**After user selection, confirm before proceeding:**
```
questions:
  - question: Ready to finalize the implementation plan with this approach?
    header: Confirm
    multiSelect: false
    options:
      - label: Yes, write the plan
        description: Finalize plan with selected architecture
      - label: Explore more
        description: I have more questions or want to reconsider
```

**Output:** Selected architecture approach with user approval.

---

### Phase 5: Write the Plan (REQUIRED)

**Goal:** Document the complete implementation plan.

**You MUST write the plan to `.ralph/plans/TASK-ID.md`** - this is not optional.

**Plan must include:**
- Selected architecture approach and rationale
- Specification impact: specs consulted, spec modifications required, interface changes, existing drift
- Patterns discovered during exploration (with file references)
- Step-by-step implementation sequence with file paths, line numbers, current code snippets, and precise change descriptions
- Module impact summary and whether modules should be combined or reorganized
- Critical files table (CREATE/MODIFY/REFERENCE with line ranges)
- Optimization goals: whether this simplifies or adds complexity
- Future considerations: migration, compatibility, follow-up work
- Testing plan: specific tests to add/modify/run, with success criteria
- Potential challenges and mitigations
- Decisions made during clarifying questions

For plan structure and format, see references/plan-format.md.

---

### Phase 5.5: Add Task to Kanban (when task was designed in Phase 0)

**Skip this phase if the task already existed in kanban.**

Now that the plan is written, add the task entry to `.ralph/kanban.md`:

- Add properly formatted task entry using the ID determined in Phase 0
- Include all required fields: Description, Priority, Dependencies
- Use optional fields (Scope, Acceptance Criteria) when helpful
- Confirm with user before writing via AskUserQuestion

**Why plan-first?** Writing the plan before the kanban entry ensures the task is fully thought through before it becomes visible to the scheduler. A task with a plan already attached is immediately actionable by workers.

---

### Phase 6: Summary

**Goal:** Document accomplishments and provide clear next steps.

**Present summary to user:**
- What was planned and why
- Key architectural decisions made
- Specification changes required (if any)
- Interface surface impact (narrower/same/wider)
- Critical files identified
- Potential challenges flagged
- Suggested next steps (run worker, need more planning, etc.)

**Output:** User has clear understanding of the plan and confidence to proceed.

## Key Principles

1. **NEVER implement** - Planning only, no code changes. Your deliverable is a `.ralph/plans/TASK-ID.md` file, not code.
2. **NEVER enter plan mode** - Do NOT use `EnterPlanMode`. This skill IS the planning mechanism.
3. **ALWAYS write the plan file** - Every planning session must result in writing `.ralph/plans/TASK-ID.md`. If you don't write the file, you failed.
4. **Check existing task IDs first** - Read kanban before creating plans to understand the task landscape
5. **Check related tasks and plans** - Read dependency tasks and their plans; understand what they provide and expect
6. **Research before exploring** - Understand requirements, specs, and system architecture before diving into code
7. **Specs are source of truth** - Explore `spec/` to understand existing specifications; plan must account for spec fit and required changes
8. **Follow the phases** - Task Design → Research → Exploration → Questions → Architecture → Plan → Kanban → Summary
9. **Parallel exploration** - Analyze similar features, architecture, integration points, and interfaces/coupling together
10. **Minimize interface surface** - Prefer designs that reduce coupling between modules, not extend it
11. **Questions are critical** - Phase 3 is one of the most important; never skip it
12. **Multiple approaches** - Present 2-3 architecture options with trade-off analysis
13. **Get approval** - Confirm architecture choice before writing plan
14. **Ground in findings** - Every option must reference actual codebase patterns and spec documents
15. **Audit mode for no argument** - When invoked without argument, list unplanned tasks grouped logically; don't auto-plan

## Progressive Disclosure

This SKILL.md contains the core workflow. For detailed guidance:
- **Plan format**: references/plan-format.md
- **Exploration strategies**: references/exploration-strategies.md
- **Question patterns**: references/question-patterns.md
