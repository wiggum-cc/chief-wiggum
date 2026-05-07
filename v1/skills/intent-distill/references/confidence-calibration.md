# Confidence Calibration Guide

Confidence scores indicate how certain the extraction is, based on pattern frequency and structural consistency across the codebase.

## Scoring Thresholds

| Score | Evidence Required | Guidance |
|-------|-------------------|----------|
| **0.9 - 1.0** | Pattern in 5+ locations with consistent structure | High confidence. The pattern is clearly intentional and pervasive. |
| **0.7 - 0.89** | Pattern in 3-4 locations with minor variations | Good confidence. Variations may indicate the pattern is evolving. |
| **0.5 - 0.69** | Pattern in 1-2 locations but structurally significant | Moderate confidence. May be an emerging pattern or isolated convention. |
| **< 0.5** | Insufficient evidence | **Do not emit.** Not enough data to justify distillation. |

## Adjustments

### Upward Adjustments (+0.05 to +0.15)

- **Naming consistency**: All instances use the same naming convention
- **Documentation alignment**: Pattern matches what README/docs describe
- **Test coverage**: Pattern has dedicated tests validating its behavior
- **Error handling**: All instances handle errors the same way
- **Configuration**: Pattern is parameterized via config, suggesting intentional design

### Downward Adjustments (-0.05 to -0.15)

- **Variations between instances**: Some locations deviate from the core pattern
- **Dead code presence**: Some instances appear unused or deprecated
- **TODO/FIXME markers**: Comments suggest the pattern is provisional
- **Inconsistent error handling**: Different instances handle failures differently
- **Mixed conventions**: Some instances follow the pattern, others don't

## Examples

### High Confidence (0.92)
> "All 7 HTTP handlers in `src/handlers/` follow the same middleware chain: auth -> validate -> execute -> respond. No exceptions found."

**Why 0.92**: 7 instances, zero variation, clear structural consistency.

### Medium Confidence (0.75)
> "Retry logic with exponential backoff found in 3 client implementations. Two use identical parameters, one uses a shorter max delay."

**Why 0.75**: 3 instances (above the 3-location threshold for 0.7+), but one varies.

### Low Confidence (0.55)
> "Resource cleanup pattern (acquire-use-release) found in database and cache modules. Similar structure but different error recovery."

**Why 0.55**: 2 locations, structurally similar but with meaningful differences in error handling.

### Below Threshold (0.4 - do not emit)
> "Custom serialization found in one utility file. No other modules use this approach."

**Why excluded**: Single instance with no corroboration. Could be a one-off solution rather than an architectural pattern.

## Calibration Checklist

Before finalizing a confidence score, verify:

1. **Count locations** - How many files/functions exhibit this pattern?
2. **Check consistency** - Do all instances follow the same structure?
3. **Look for exceptions** - Are there places where this pattern SHOULD apply but doesn't?
4. **Assess intentionality** - Does this look deliberate (documented, tested) or accidental (copy-paste)?
5. **Consider scope** - Is this a codebase-wide pattern or module-local convention?
