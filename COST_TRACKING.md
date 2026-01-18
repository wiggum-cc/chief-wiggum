# Cost and Time Tracking Implementation

This document describes the cost and time tracking features added to Chief Wiggum workers.

## Overview

Each worker run now tracks:
- **Time spent**: Total execution time from start to finish
- **API cost**: Estimated cost based on Claude Sonnet 4.5 pricing (2026)
- **Token usage**: Detailed breakdown of input, output, cache creation, and cache read tokens

## Implementation Details

### Files Modified

1. **lib/calculate-cost.sh** (new)
   - Parses worker.log files to extract token usage from JSON output
   - Calculates time spent using timestamp markers
   - Computes cost based on current Claude API pricing
   - Exports metrics as environment variables for use in PR summaries

2. **lib/ralph-loop.sh**
   - Added `WORKER_START_TIME` timestamp marker at loop start (line 17-18)
   - Added `WORKER_END_TIME` timestamp marker at loop end (line 131-132)
   - These markers enable accurate time tracking

3. **lib/worker.sh**
   - Sources the calculate-cost.sh script (line 15)
   - Calls cost calculation before creating PR (line 205)
   - Includes metrics section in PR body (lines 208-220)

### Cost Calculation Method

The script uses the following Claude Sonnet 4.5 pricing (as of 2026):

| Token Type | Price per Million Tokens |
|-----------|-------------------------|
| Input tokens | $3.00 |
| Output tokens | $15.00 |
| Cache creation tokens | $3.00 |
| Cache read tokens | $0.30 (10% of input) |

**Formula:**
```
Total Cost = (input_tokens × $3.00 / 1M) +
             (output_tokens × $15.00 / 1M) +
             (cache_creation_tokens × $3.00 / 1M) +
             (cache_read_tokens × $0.30 / 1M)
```

### Time Tracking Method

Time is calculated using one of these methods (in order of preference):

1. **Timestamp markers**: `WORKER_START_TIME` and `WORKER_END_TIME` markers in log
2. **File timestamps**: Creation and modification times of worker.log
3. **Iteration estimate**: Number of iterations × 30 seconds (fallback)

### PR Summary Format

The metrics are included in the PR body as follows:

```markdown
## Metrics

**Time Spent:** HH:MM:SS
**API Cost:** $X.XXXXXX (Sonnet 4.5)

**Token Usage:**
- Input: XXX,XXX tokens
- Output: XXX,XXX tokens
- Cache creation: XXX,XXX tokens
- Cache read: XXX,XXX tokens
```

## Usage

### Manual Cost Calculation

To manually calculate costs for a worker run:

```bash
bash lib/calculate-cost.sh /path/to/worker.log
```

### Automatic Integration

The cost calculation is automatically performed during worker cleanup when creating PRs. No manual intervention required.

## Example Output

```
=== Worker Time and Cost Report ===

Time Spent: 00:06:00 (360 seconds)

Token Usage:
  Input tokens: 294
  Output tokens: 6,163
  Cache creation tokens: 188,344
  Cache read tokens: 1,205,070
  Total tokens: 1,399,871

Cost Breakdown (Claude Sonnet 4.5):
  Input tokens: $0.000882
  Output tokens: $0.092445
  Cache creation: $0.565032
  Cache read: $0.361521
  Total cost: $1.019880
```

## References

- [Claude API Pricing (2026)](https://platform.claude.com/docs/en/about-claude/pricing)
- [Claude API Cost Calculator](https://costgoat.com/pricing/claude-api)
- [Claude Code Pricing Guide](https://blog.promptlayer.com/claude-code-pricing-how-to-save-money/)

## Future Enhancements

Potential improvements:
1. Add cost tracking to changelog entries
2. Aggregate costs across all workers in a session
3. Add budget alerts/warnings
4. Support different model pricing (Haiku, Opus)
5. Track cost trends over time
