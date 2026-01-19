#!/usr/bin/env bash
# Convert JSONL iteration log to markdown for resume context
# Usage: log-converter.sh <iteration-log.jsonl> [output.md]
#
# Processes line by line (each JSON object is one line), uses jq for parsing.

set -euo pipefail

INPUT_FILE="${1:-}"
OUTPUT_FILE="${2:-/dev/stdout}"

if [ -z "$INPUT_FILE" ] || [ ! -f "$INPUT_FILE" ]; then
    echo "Usage: log-converter.sh <iteration-log.jsonl> [output.md]" >&2
    echo "Converts Claude CLI stream-JSON logs to readable markdown." >&2
    exit 1
fi

# Maximum size for content truncation
MAX_SIZE=2000

# Truncate long strings
truncate_str() {
    local str="$1"
    local max="${2:-$MAX_SIZE}"
    local len=${#str}
    if [ "$len" -gt "$max" ]; then
        echo "${str:0:$max}"
        echo ""
        echo "[... truncated $((len - max)) characters ...]"
    else
        echo "$str"
    fi
}

# Process the file and output markdown
{
    echo "# Conversation Log"
    echo ""

    while IFS= read -r line || [ -n "$line" ]; do
        [ -z "$line" ] && continue

        # Get the type field
        type=$(echo "$line" | jq -r '.type // empty' 2>/dev/null) || continue
        [ -z "$type" ] && continue

        case "$type" in
            iteration_start)
                iter=$(echo "$line" | jq -r '.iteration // "?"')
                session=$(echo "$line" | jq -r '.session_id // "unknown"')
                echo "**Iteration:** $iter"
                echo "**Session:** ${session:0:8}..."
                echo ""
                echo "---"
                echo ""
                ;;

            assistant)
                # Get content array length
                content_len=$(echo "$line" | jq '.message.content | length' 2>/dev/null) || continue

                for ((i=0; i<content_len; i++)); do
                    content_type=$(echo "$line" | jq -r ".message.content[$i].type // empty")

                    case "$content_type" in
                        text)
                            text=$(echo "$line" | jq -r ".message.content[$i].text // empty")
                            if [ -n "$text" ]; then
                                echo "## Assistant"
                                echo ""
                                echo "$text"
                                echo ""
                            fi
                            ;;

                        tool_use)
                            tool_name=$(echo "$line" | jq -r ".message.content[$i].name // \"unknown\"")
                            tool_input=$(echo "$line" | jq ".message.content[$i].input // {}" 2>/dev/null)

                            echo "## Tool: $tool_name"
                            echo ""
                            echo "**Input:**"
                            echo '```json'
                            truncate_str "$tool_input" 1000
                            echo '```'
                            echo ""
                            ;;
                    esac
                done
                ;;

            user)
                # Check for tool_result
                content_type=$(echo "$line" | jq -r '.message.content[0].type // empty' 2>/dev/null) || continue

                if [ "$content_type" = "tool_result" ]; then
                    result_content=$(echo "$line" | jq -r '.message.content[0].content // empty')
                    is_error=$(echo "$line" | jq -r '.message.content[0].is_error // false')

                    if [ "$is_error" = "true" ]; then
                        echo "**Result (error):**"
                    else
                        echo "**Result:**"
                    fi

                    echo '```'
                    truncate_str "$result_content" "$MAX_SIZE"
                    echo '```'
                    echo ""
                    echo "---"
                    echo ""
                fi
                ;;

            iteration_complete)
                exit_code=$(echo "$line" | jq -r '.work_exit_code // "?"')
                echo ""
                echo "---"
                echo "**Iteration completed** (exit code: $exit_code)"
                echo ""
                ;;

            result)
                total_cost=$(echo "$line" | jq -r '.total_cost_usd // 0')
                duration=$(echo "$line" | jq -r '.duration_ms // 0')
                if [ "$total_cost" != "0" ] || [ "$duration" != "0" ]; then
                    echo ""
                    echo "---"
                    echo "**Session stats:** Cost: \$$total_cost, Duration: ${duration}ms"
                fi
                ;;
        esac

    done < "$INPUT_FILE"

    echo ""
    echo "---"
    echo "*Log converted from $(basename "$INPUT_FILE")*"

} > "$OUTPUT_FILE"

echo "Converted $(basename "$INPUT_FILE") to markdown" >&2
