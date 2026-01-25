# Plan Format Reference

## Plan File Structure

Plans are written to `.ralph/plans/TASK-ID.md`.

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
| File | Action | Reason |
|------|--------|--------|
| path/file.ext | CREATE | [Purpose] |
| path/file.ext | MODIFY | [What changes] |
| path/file.ext | REFERENCE | [Pattern to follow] |

### Incompatible With (only if applicable)
TASK-029
```

## Section Details

### Overview
- 1-2 sentences maximum
- State what and why, not how
- Connect to business value if relevant

### Requirements Analysis
Table format for clarity:
- Extract from task's Scope and Acceptance Criteria
- Add complexity estimate per requirement
- Include any implicit requirements discovered

### Existing Patterns
Critical for consistency:
- Reference actual file paths
- Describe the pattern briefly
- Explain why this pattern applies

### Implementation Approach
Step-by-step with specifics:
- Number each step
- Include file paths
- Describe actual changes (not vague "update X")
- Order by dependency

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

### Critical Files
Table format required:
- **CREATE**: New files to create
- **MODIFY**: Existing files to change
- **REFERENCE**: Files to use as patterns (don't modify)
- List 3-5 most important files

### Incompatible With
Only include if applicable:
- List task IDs that conflict with this implementation
- Explain why in the Potential Challenges section
- These tasks may need to be marked `[N]` Not Planned

## Quality Checklist

Before finalizing plan:
- [ ] All file paths are real (verified via exploration)
- [ ] Patterns reference actual codebase examples
- [ ] Steps are specific and actionable
- [ ] Critical Files table has 3-5 entries
- [ ] Challenges section addresses real risks
- [ ] Requirements map to task's Acceptance Criteria
