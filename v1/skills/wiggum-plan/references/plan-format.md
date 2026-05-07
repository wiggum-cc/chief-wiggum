# Plan Format Reference

## Plan File Structure

Plans are written to `.ralph/plans/TASK-ID.md`.

```markdown
# Implementation Plan: [TASK-ID]

## Overview
[1-2 sentences: what will be implemented and why]

## Architecture Context
[Describe the current architecture of the subsystems this task touches.
How do the relevant modules fit together? What are their responsibilities
and boundaries? Structural overview for an engineer unfamiliar with this area.]

## Architectural Decisions
[For each significant design choice this task requires:]
- **Decision**: [What needs to be decided]
- **Options considered**: [Alternatives evaluated]
- **Chosen approach**: [What and why]
- **Trade-offs**: [What is gained, what is sacrificed]

## Optimization Goals
[What does this implementation optimize for? Does it reduce system complexity?
Does it consolidate existing ad-hoc solutions? Are new abstractions justified?]

## Specification Impact

### Specs Consulted
| Spec Document | Sections Relevant | Current Status |
|---------------|-------------------|----------------|
| [doc path] | [section names] | [aligned / drifted / not covered] |

### Spec Modifications Required
- **Document**: [path]
- **Current spec text**: [quote the relevant section]
- **Proposed change**: [what to add, modify, or remove]
- **Reason**: [why the spec must change to accommodate this task]

If no spec changes are needed, state: "All requirements fit within existing specifications."

### Interface Changes
- **Interface**: [function signature, file format, schema, config key]
- **Between**: [module A] <-> [module B]
- **Current contract**: [what it is now]
- **Proposed contract**: [what it becomes]
- **Surface change**: [narrower / same / wider] — prefer narrower

### Existing Spec Drift
- [file:line] deviates from [spec:section] — [description]

## Requirements Traceability
| Req | Source | Spec Text | Acceptance Criteria | Approach |
|-----|--------|-----------|---------------------|----------|
| R1 | PRD/spec/docs | [exact text] | [verify done] | [technical] |

CRITICAL: Every requirement from PRD AND relevant spec/ documents must appear here.

## Existing Patterns
| Pattern | Location | Relevance |
|---------|----------|-----------|
| [name] | [file:line] | [how to use] |

## Implementation Steps
1. **[Step title]** - Implements R1
   - **Module**: [which module/subsystem]
   - **File**: `path/to/file.sh:LINE`
   - **Current code**:
     ```
     [relevant snippet of what exists now]
     ```
   - **Change**: [precise description of what to add/modify/remove]
   - **Rationale**: [why this change, how it connects to the design]

## Module Impact Summary
| Module | Files Changed | Nature of Change |
|--------|--------------|------------------|
| [module] | [count] | [new/modified/refactored] |

[Note if any modules should be combined, split, or reorganized.]

## Future Considerations
- [Migration of existing data/config?]
- [Backward-compatibility concerns?]
- [Future work this enables or constrains?]

## Dependencies and Sequencing
[Order of operations, what depends on what]

## Potential Challenges
[Technical risks, edge cases, things to watch out for]

## Testing Plan

### Tests to Add
| Test | Type | File | What It Validates |
|------|------|------|-------------------|
| [test name] | unit/integration/e2e | [path] | [behavior verified] |

### Tests to Modify
| Test | File | Why |
|------|------|-----|
| [test name] | [path] | [what changed that requires update] |

### Existing Tests to Run
[List specific test files/suites that must pass after implementation]

### Success Criteria
- [ ] [Specific, verifiable criterion]
- [ ] [All existing tests pass]
- [ ] [New tests cover added/changed behavior]

## Integration Checklist
- [ ] Entry point wired
- [ ] Configuration connected
- [ ] Tests planned
- [ ] Docs identified

## Critical Files
| File | Action | Lines | Requirement |
|------|--------|-------|-------------|
| path/file.sh:L10-L45 | CREATE | [line range] | R1 |
| path/other.sh:L5-L20 | MODIFY | [line range] | R2 |
| tests/main.rs:L1-L5 | MODIFY(minor) | [line range] | R2 |
| path/pattern.sh:L30-L60 | REFERENCE | — | [pattern to follow] |

Actions: **CREATE** (new file), **MODIFY** (change existing), **MODIFY(minor)** (trivial/auto-mergeable change, e.g. test harness registration — excluded from conflict detection), **REFERENCE** (pattern to follow, do not modify)

### Incompatible With (only if applicable)
TASK-029
```

## Section Details

### Overview
- 1-2 sentences maximum
- State what and why, not how
- Connect to business value if relevant

### Architecture Context
Provides orientation for the implementing engineer:
- Describe the relevant subsystems and how they interconnect
- Explain module responsibilities and communication patterns
- Include enough structure that someone unfamiliar can reason about the changes

### Architectural Decisions
For each non-trivial design choice:
- State the decision clearly
- List alternatives that were considered
- Explain why the chosen approach was selected
- Be honest about trade-offs — what is sacrificed

### Optimization Goals
Explicit about what the implementation aims to achieve:
- Does it simplify the system or add complexity?
- Can new requirements be absorbed by existing abstractions?
- Are there consolidation opportunities?
- Are new abstractions justified by the scope?

### Specification Impact
Ties the plan back to the project's spec-driven development practice.

Specs live in `spec/` (source of truth). Do not assume internal structure — explore and discover.
- **Specs Consulted**: Which spec documents in `spec/` were read and whether current code aligns with them
- **Spec Modifications Required**: Quote the current spec text and propose the minimal change needed. Specs are authoritative — if the spec needs to change, be explicit about what and why
- **Interface Changes**: For each module boundary affected, state the current contract, proposed contract, and whether the interface surface gets narrower, stays the same, or gets wider. Always prefer narrower
- **Existing Spec Drift**: If code already deviates from spec, flag it. The plan should correct drift, not build on top of it

### Requirements Traceability
Table format linking requirements to implementation:
- Every PRD and spec/ requirement must have a row
- Include acceptance criteria for verification
- Map each to the technical approach

### Existing Patterns
Critical for consistency:
- Reference actual file paths with line numbers
- Describe the pattern briefly
- Explain why this pattern applies

### Implementation Steps
Precise and actionable with code context:
- Number each step
- Include file paths with line numbers
- Show the current code snippet that will be changed
- Describe the exact change (not vague "update X")
- State the rationale connecting to the design
- Order by dependency

### Module Impact Summary
Birds-eye view of which parts of the system are affected:
- Count of files changed per module
- Nature of changes (new code, modifications, refactoring)
- Note if modules should be combined or reorganized

### Future Considerations
Forward-looking analysis:
- Migration requirements for existing data or config
- Backward-compatibility concerns
- Follow-up work this creates or enables

### Dependencies and Sequencing
- Internal: which steps depend on others
- External: task dependencies from kanban
- Note any blocking factors

### Potential Challenges
Document risks upfront:
- Technical complexity
- Edge cases to handle
- Integration points that might fail
- Performance considerations

### Testing Plan
Explicit and specific:
- **Tests to Add**: new tests with type, file path, and what they validate
- **Tests to Modify**: existing tests that need updates due to behavioral changes
- **Existing Tests to Run**: specific suites that must pass
- **Success Criteria**: verifiable checklist of what "done" means

### Critical Files
Table format required:
- **CREATE**: New files to create
- **MODIFY**: Existing files to change (with line ranges)
- **MODIFY(minor)**: Trivially auto-mergeable changes (e.g., adding a `mod` line to a test harness, appending to a list). Excluded from conflict detection so concurrent tasks touching the same file aren't blocked
- **REFERENCE**: Files to use as patterns (don't modify)
- List all significant files (not just 3-5)

### Incompatible With
Only include if applicable:
- List task IDs that conflict with this implementation
- Explain why in the Potential Challenges section
- These tasks may need to be marked `[N]` Not Planned

## Quality Checklist

Before finalizing plan:
- [ ] All file paths are real (verified via exploration)
- [ ] File references include line numbers, not just paths
- [ ] Implementation steps include current code snippets
- [ ] Patterns reference actual codebase examples
- [ ] Steps are specific and actionable — no vague language
- [ ] Architecture context orients someone unfamiliar with the area
- [ ] Architectural decisions list alternatives and trade-offs
- [ ] Optimization goals state whether complexity increases or decreases
- [ ] Specification Impact lists specs consulted with alignment status
- [ ] Spec modifications quote current text and propose minimal changes
- [ ] Interface changes state surface direction (narrower/same/wider)
- [ ] Existing spec drift is flagged, not ignored
- [ ] Testing plan has specific tests, files, and success criteria
- [ ] Critical Files table has line ranges
- [ ] Challenges section addresses real risks
- [ ] Requirements map to task's Acceptance Criteria
