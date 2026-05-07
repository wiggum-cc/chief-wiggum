#!/usr/bin/env bash
# log-converter.sh - Convert JSONL iteration logs to readable conversation markdown
#
# Modes:
#   Single file: log-converter.sh <agent-log.jsonl> [output.md]
#   Directory:   log-converter.sh --dir <worker_dir>
#
# In directory mode, processes all iteration and sub-agent logs in a worker
# directory, producing readable markdown files in a conversations/ subdirectory.
# Used by the system.resume-decide agent to understand what happened in a previous run.

set -euo pipefail

[ -z "${_WIGGUM_SRC_PLATFORM_LOADED:-}" ] && source "$WIGGUM_HOME/lib/core/platform.sh"

# Maximum size for content truncation
MAX_CONTENT=3000
MAX_TOOL_INPUT=1500
MAX_TOOL_RESULT=2000

# Truncate long strings
_truncate() {
    local str="$1"
    local max="${2:-$MAX_CONTENT}"
    local len=${#str}
    if [ "$len" -gt "$max" ]; then
        echo "${str:0:$max}"
        echo ""
        echo "[... truncated $((len - max)) characters ...]"
    else
        echo "$str"
    fi
}

# Convert a single JSONL log file to conversation markdown
# Groups tool_use with corresponding tool_result by tool_use_id
#
# Args:
#   input_file  - Path to the .log JSONL file
#   output_file - Path to write the .md output (default: /dev/stdout)
convert_log() {
    local input_file="$1"
    local output_file="${2:-/dev/stdout}"
    local log_basename
    log_basename=$(basename "$input_file" .log)

    {
        echo "# Conversation: $log_basename"
        echo ""

        # Track pending tool uses (id -> name mapping)
        declare -A pending_tools=()

        while IFS= read -r line || [ -n "$line" ]; do
            [ -z "$line" ] && continue

            local msg_type
            msg_type=$(echo "$line" | jq -r '.type // empty' 2>/dev/null) || continue
            [ -z "$msg_type" ] && continue

            case "$msg_type" in
                iteration_start)
                    local iter session
                    iter=$(echo "$line" | jq -r '.iteration // "?"')
                    session=$(echo "$line" | jq -r '.session_id // "unknown"')
                    echo "---"
                    echo "**Iteration $iter** (session: ${session:0:12}...)"
                    echo ""
                    ;;

                assistant)
                    local content_len
                    content_len=$(echo "$line" | jq '.message.content | length' 2>/dev/null) || continue

                    for ((i=0; i<content_len; i++)); do
                        local content_type
                        content_type=$(echo "$line" | jq -r ".message.content[$i].type // empty")

                        case "$content_type" in
                            text)
                                local text
                                text=$(echo "$line" | jq -r ".message.content[$i].text // empty")
                                if [ -n "$text" ]; then
                                    echo "## Assistant"
                                    echo ""
                                    _truncate "$text" "$MAX_CONTENT"
                                    echo ""
                                fi
                                ;;

                            tool_use)
                                local tool_id tool_name tool_input
                                tool_id=$(echo "$line" | jq -r ".message.content[$i].id // empty")
                                tool_name=$(echo "$line" | jq -r ".message.content[$i].name // \"unknown\"")
                                tool_input=$(echo "$line" | jq -c ".message.content[$i].input // {}" 2>/dev/null)

                                # Track this tool use for later matching with result
                                if [ -n "$tool_id" ]; then
                                    pending_tools["$tool_id"]="$tool_name"
                                fi

                                echo "### Tool: $tool_name"
                                echo ""

                                # Show relevant input fields based on tool type
                                case "$tool_name" in
                                    Read|read)
                                        local file_path
                                        file_path=$(echo "$tool_input" | jq -r '.file_path // .path // empty')
                                        echo "**File:** \`$file_path\`"
                                        ;;
                                    Write|write)
                                        local file_path
                                        file_path=$(echo "$tool_input" | jq -r '.file_path // .path // empty')
                                        echo "**File:** \`$file_path\`"
                                        echo ""
                                        echo "<details><summary>Content</summary>"
                                        echo ""
                                        echo '```'
                                        local content
                                        content=$(echo "$tool_input" | jq -r '.content // empty')
                                        _truncate "$content" "$MAX_TOOL_INPUT"
                                        echo '```'
                                        echo ""
                                        echo "</details>"
                                        ;;
                                    Edit|edit)
                                        local file_path
                                        file_path=$(echo "$tool_input" | jq -r '.file_path // .path // empty')
                                        echo "**File:** \`$file_path\`"
                                        echo ""
                                        echo "Old:"
                                        echo '```'
                                        local old_str
                                        old_str=$(echo "$tool_input" | jq -r '.old_string // empty')
                                        _truncate "$old_str" 500
                                        echo '```'
                                        echo "New:"
                                        echo '```'
                                        local new_str
                                        new_str=$(echo "$tool_input" | jq -r '.new_string // empty')
                                        _truncate "$new_str" 500
                                        echo '```'
                                        ;;
                                    Bash|bash)
                                        echo '```bash'
                                        local cmd
                                        cmd=$(echo "$tool_input" | jq -r '.command // empty')
                                        _truncate "$cmd" "$MAX_TOOL_INPUT"
                                        echo '```'
                                        ;;
                                    Glob|grep|Grep)
                                        echo "**Pattern:** \`$(echo "$tool_input" | jq -r '.pattern // empty')\`"
                                        local path
                                        path=$(echo "$tool_input" | jq -r '.path // empty')
                                        [ -n "$path" ] && echo "**Path:** \`$path\`"
                                        ;;
                                    *)
                                        echo '```json'
                                        _truncate "$tool_input" "$MAX_TOOL_INPUT"
                                        echo '```'
                                        ;;
                                esac
                                echo ""
                                ;;
                        esac
                    done
                    ;;

                user)
                    # Process tool results and associate with their tool_use
                    local content_len
                    content_len=$(echo "$line" | jq '.message.content | length' 2>/dev/null) || continue

                    for ((i=0; i<content_len; i++)); do
                        local content_type
                        content_type=$(echo "$line" | jq -r ".message.content[$i].type // empty" 2>/dev/null)

                        if [ "$content_type" = "tool_result" ]; then
                            local tool_use_id result_content is_error
                            tool_use_id=$(echo "$line" | jq -r ".message.content[$i].tool_use_id // empty")
                            is_error=$(echo "$line" | jq -r ".message.content[$i].is_error // false")

                            # Get the result content (may be string or array of content blocks)
                            result_content=$(echo "$line" | jq -r "
                                .message.content[$i].content //
                                .message.content[$i].output // empty
                            " 2>/dev/null)

                            # If content is an array (multi-part result), extract text
                            if jq -e 'type == "array"' <<< "$result_content" >/dev/null 2>&1; then
                                result_content=$(jq -r '.[] | select(.type == "text") | .text' <<< "$result_content" 2>/dev/null)
                            fi

                            # Find matching tool name
                            local matched_tool="${pending_tools[$tool_use_id]:-}"

                            if [ "$is_error" = "true" ]; then
                                echo "**Result** (${matched_tool:-tool} - ERROR):"
                            else
                                echo "**Result** (${matched_tool:-tool}):"
                            fi

                            echo '```'
                            _truncate "$result_content" "$MAX_TOOL_RESULT"
                            echo '```'
                            echo ""

                            # Clear from pending
                            unset "pending_tools[$tool_use_id]" 2>/dev/null || true
                        fi
                    done
                    ;;

                iteration_complete)
                    local exit_code
                    exit_code=$(echo "$line" | jq -r '.work_exit_code // "?"')
                    echo ""
                    echo "---"
                    echo "**Iteration completed** (exit code: $exit_code)"
                    echo ""
                    ;;

                result)
                    local total_cost duration
                    total_cost=$(echo "$line" | jq -r '.total_cost_usd // 0')
                    duration=$(echo "$line" | jq -r '.duration_ms // 0')
                    if [ "$total_cost" != "0" ] || [ "$duration" != "0" ]; then
                        echo "**Stats:** Cost: \$$total_cost, Duration: ${duration}ms"
                        echo ""
                    fi
                    ;;
            esac
        done < "$input_file"

        echo ""
        echo "---"
        echo "*Converted from $(basename "$input_file")*"

    } > "$output_file"
}

# Convert all logs in a worker directory
convert_dir() {
    local worker_dir="$1"
    local logs_dir="$worker_dir/logs"
    local conv_dir="$worker_dir/conversations"

    if [ ! -d "$logs_dir" ]; then
        echo "No logs directory found at $logs_dir" >&2
        exit 0
    fi

    mkdir -p "$conv_dir"

    local converted=0 skipped=0

    # Process all agent logs in time order (searches subdirectories)
    # Matches any log file with format: {step-id}-{iteration}[-{timestamp}].log
    # Excludes summary logs which have different structure
    while IFS= read -r log_file; do
        [ -f "$log_file" ] || continue
        local local_name
        local_name=$(basename "$log_file" .log)

        # Skip already-converted files (log files are written once, never modified)
        if [ -f "$conv_dir/${local_name}.md" ]; then
            ((++skipped))
            continue
        fi

        convert_log "$log_file" "$conv_dir/${local_name}.md"
        ((++converted))
    done < <(find_sorted_by_mtime "$logs_dir" -name "*.log" ! -name "*summary*")

    if [ "$skipped" -gt 0 ]; then
        echo "Converted $converted log files ($skipped already converted) to conversations in $conv_dir" >&2
    else
        echo "Converted $converted log files to conversations in $conv_dir" >&2
    fi
}

# --- Main ---

if [ "${1:-}" = "--dir" ]; then
    # Directory mode
    WORKER_DIR="${2:-}"
    if [ -z "$WORKER_DIR" ] || [ ! -d "$WORKER_DIR" ]; then
        echo "Usage: log-converter.sh --dir <worker_dir>" >&2
        echo "Converts all worker logs to readable conversation markdown." >&2
        exit 1
    fi
    convert_dir "$WORKER_DIR"
else
    # Single file mode
    INPUT_FILE="${1:-}"
    OUTPUT_FILE="${2:-/dev/stdout}"
    if [ -z "$INPUT_FILE" ] || [ ! -f "$INPUT_FILE" ]; then
        echo "Usage: log-converter.sh <agent-log.jsonl> [output.md]" >&2
        echo "       log-converter.sh --dir <worker_dir>" >&2
        echo "Converts Claude CLI stream-JSON logs to readable markdown." >&2
        exit 1
    fi
    convert_log "$INPUT_FILE" "$OUTPUT_FILE"
    [ "$OUTPUT_FILE" != "/dev/stdout" ] && echo "Converted $(basename "$INPUT_FILE") to markdown" >&2
fi
