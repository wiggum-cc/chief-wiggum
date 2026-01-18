#!/usr/bin/env bash
# Calculate time spent and API cost from worker logs

calculate_worker_cost() {
    local log_file="$1"

    if [ ! -f "$log_file" ]; then
        echo "Error: Log file not found: $log_file" >&2
        return 1
    fi

    # Extract all token usage from the log
    local input_tokens=0
    local output_tokens=0
    local cache_creation_tokens=0
    local cache_read_tokens=0

    # Parse JSON lines for token usage
    while IFS= read -r line; do
        # Extract input_tokens (excluding cache fields)
        local it=$(echo "$line" | grep -o '"input_tokens":[0-9]*' | head -1 | cut -d':' -f2)
        [ -n "$it" ] && input_tokens=$((input_tokens + it))

        # Extract output_tokens
        local ot=$(echo "$line" | grep -o '"output_tokens":[0-9]*' | head -1 | cut -d':' -f2)
        [ -n "$ot" ] && output_tokens=$((output_tokens + ot))

        # Extract cache_creation_input_tokens
        local cct=$(echo "$line" | grep -o '"cache_creation_input_tokens":[0-9]*' | head -1 | cut -d':' -f2)
        [ -n "$cct" ] && cache_creation_tokens=$((cache_creation_tokens + cct))

        # Extract cache_read_input_tokens
        local crt=$(echo "$line" | grep -o '"cache_read_input_tokens":[0-9]*' | head -1 | cut -d':' -f2)
        [ -n "$crt" ] && cache_read_tokens=$((cache_read_tokens + crt))
    done < <(grep '"input_tokens"' "$log_file")

    # Calculate time spent from log timestamps
    local time_spent=0

    # Try to get exact timestamps from log markers
    local start_ts=$(grep "WORKER_START_TIME=" "$log_file" | head -1 | cut -d'=' -f2)
    local end_ts=$(grep "WORKER_END_TIME=" "$log_file" | tail -1 | cut -d'=' -f2)

    if [ -n "$start_ts" ] && [ -n "$end_ts" ] && [ "$end_ts" -gt "$start_ts" ]; then
        time_spent=$((end_ts - start_ts))
    else
        # Fallback: use file timestamps
        local log_start=$(stat -c %Y "$log_file" 2>/dev/null || stat -f %B "$log_file" 2>/dev/null || echo 0)
        local log_end=$(stat -c %Y "$log_file" 2>/dev/null || stat -f %m "$log_file" 2>/dev/null || echo 0)

        if [ "$log_end" -gt "$log_start" ]; then
            time_spent=$((log_end - log_start))
        else
            # Last resort: estimate from number of iterations
            local iterations=$(grep -c "=== ITERATION" "$log_file")
            # Rough estimate: 30 seconds per iteration on average
            time_spent=$((iterations * 30))
        fi
    fi

    # Format time as HH:MM:SS
    local hours=$((time_spent / 3600))
    local minutes=$(((time_spent % 3600) / 60))
    local seconds=$((time_spent % 60))
    local time_formatted=$(printf "%02d:%02d:%02d" $hours $minutes $seconds)

    # Calculate costs based on Claude Sonnet 4.5 pricing (2026)
    # Input: $3.00 per million tokens
    # Output: $15.00 per million tokens
    # Cache creation: same as input ($3.00 per million)
    # Cache read: $0.30 per million (0.1x of input)

    local cost_input=$(echo "scale=6; ($input_tokens * 3.00) / 1000000" | bc)
    local cost_output=$(echo "scale=6; ($output_tokens * 15.00) / 1000000" | bc)
    local cost_cache_creation=$(echo "scale=6; ($cache_creation_tokens * 3.00) / 1000000" | bc)
    local cost_cache_read=$(echo "scale=6; ($cache_read_tokens * 0.30) / 1000000" | bc)
    local total_cost=$(echo "scale=6; $cost_input + $cost_output + $cost_cache_creation + $cost_cache_read" | bc)

    # Output results
    echo "=== Worker Time and Cost Report ==="
    echo ""
    echo "Time Spent: $time_formatted ($time_spent seconds)"
    echo ""
    echo "Token Usage:"
    echo "  Input tokens: $(printf "%'d" $input_tokens)"
    echo "  Output tokens: $(printf "%'d" $output_tokens)"
    echo "  Cache creation tokens: $(printf "%'d" $cache_creation_tokens)"
    echo "  Cache read tokens: $(printf "%'d" $cache_read_tokens)"
    echo "  Total tokens: $(printf "%'d" $((input_tokens + output_tokens + cache_creation_tokens + cache_read_tokens)))"
    echo ""
    echo "Cost Breakdown (Claude Sonnet 4.5):"
    echo "  Input tokens: \$$(printf "%.6f" $cost_input)"
    echo "  Output tokens: \$$(printf "%.6f" $cost_output)"
    echo "  Cache creation: \$$(printf "%.6f" $cost_cache_creation)"
    echo "  Cache read: \$$(printf "%.6f" $cost_cache_read)"
    echo "  Total cost: \$$(printf "%.6f" $total_cost)"
    echo ""

    # Export for use in PR summary
    export WORKER_TIME_SPENT="$time_formatted"
    export WORKER_TOTAL_COST=$(printf "%.6f" $total_cost)
    export WORKER_INPUT_TOKENS=$input_tokens
    export WORKER_OUTPUT_TOKENS=$output_tokens
    export WORKER_CACHE_CREATION_TOKENS=$cache_creation_tokens
    export WORKER_CACHE_READ_TOKENS=$cache_read_tokens
}

# If called directly with log file argument
if [ $# -gt 0 ]; then
    calculate_worker_cost "$1"
fi
