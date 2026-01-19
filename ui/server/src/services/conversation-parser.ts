import { readdir, readFile } from "fs/promises";
import { join } from "path";

export interface TextContent {
  type: "text";
  text: string;
}

export interface ToolUseContent {
  type: "tool_use";
  id: string;
  name: string;
  input: Record<string, unknown>;
}

export interface ToolResultContent {
  type: "tool_result";
  tool_use_id: string;
  content: string;
}

export interface ConversationMessage {
  id: string;
  type: "assistant" | "user" | "system" | "iteration_start";
  timestamp?: string;
  content: (TextContent | ToolUseContent | ToolResultContent)[];
  toolResult?: unknown;
  toolUseId?: string;
  iteration?: number;
}

export interface ConversationTurn {
  assistant: ConversationMessage | null;
  toolCalls: {
    call: ToolUseContent;
    result: unknown;
  }[];
  iteration?: number;
}

export interface InitialPrompt {
  systemPrompt: string;
  userPrompt: string;
  timestamp?: string;
}

export interface IterationResult {
  iteration: number;
  subtype: string;
  durationMs: number;
  durationApiMs: number;
  numTurns: number;
  totalCostUsd: number;
  isError: boolean;
  usage: {
    inputTokens: number;
    outputTokens: number;
    cacheReadInputTokens: number;
    cacheCreationInputTokens: number;
  };
}

interface RawLogEntry {
  type: string;
  timestamp?: string;
  uuid?: string;
  message?: {
    role?: string;
    content?: Array<{
      type: string;
      text?: string;
      id?: string;
      name?: string;
      input?: Record<string, unknown>;
      tool_use_id?: string;
      content?: string;
    }>;
  };
  tool_use_result?: unknown;
  parent_tool_use_id?: string;
  session_id?: string;
  iteration?: number;
  system_prompt?: string;
  user_prompt?: string;
}

export interface ParseResult {
  messages: ConversationMessage[];
  initialPrompt: InitialPrompt | null;
  iterationResults: IterationResult[];
}

export async function parseIterationLogs(
  workerDir: string
): Promise<ParseResult> {
  const logsDir = join(workerDir, "logs");
  const messages: ConversationMessage[] = [];
  const iterationResults: IterationResult[] = [];
  let initialPrompt: InitialPrompt | null = null;

  try {
    const files = await readdir(logsDir);
    const iterationFiles = files
      .filter((f) => f.startsWith("iteration-") && f.endsWith(".log"))
      .sort((a, b) => {
        const numA = parseInt(a.match(/iteration-(\d+)/)?.[1] || "0");
        const numB = parseInt(b.match(/iteration-(\d+)/)?.[1] || "0");
        return numA - numB;
      });

    let currentIteration = 0;

    for (const file of iterationFiles) {
      const content = await readFile(join(logsDir, file), "utf-8");
      const lines = content.split("\n").filter((l) => l.trim());

      for (const line of lines) {
        try {
          const entry = JSON.parse(line);

          // Track iteration number
          if (entry.type === "iteration_start") {
            currentIteration = entry.iteration ?? currentIteration;

            // Capture initial prompt from first iteration_start
            if (!initialPrompt && (entry.system_prompt || entry.user_prompt)) {
              initialPrompt = {
                systemPrompt: entry.system_prompt || "",
                userPrompt: entry.user_prompt || "",
                timestamp: entry.timestamp,
              };
            }

            // Add iteration marker
            messages.push({
              id: `iter-start-${currentIteration}`,
              type: "iteration_start",
              timestamp: entry.timestamp,
              content: [{ type: "text", text: `Iteration ${currentIteration}` }],
              iteration: currentIteration,
            });
            continue;
          }

          // Capture iteration result/metrics
          if (entry.type === "result") {
            iterationResults.push({
              iteration: currentIteration,
              subtype: entry.subtype || "success",
              durationMs: entry.duration_ms || 0,
              durationApiMs: entry.duration_api_ms || 0,
              numTurns: entry.num_turns || 0,
              totalCostUsd: entry.total_cost_usd || 0,
              isError: entry.is_error || false,
              usage: {
                inputTokens: entry.usage?.input_tokens || 0,
                outputTokens: entry.usage?.output_tokens || 0,
                cacheReadInputTokens: entry.usage?.cache_read_input_tokens || 0,
                cacheCreationInputTokens: entry.usage?.cache_creation_input_tokens || 0,
              },
            });
            continue;
          }

          const msg = parseLogEntry(entry as RawLogEntry);
          if (msg) {
            msg.iteration = currentIteration;
            messages.push(msg);
          }
        } catch {
          // Skip invalid JSON lines
        }
      }
    }
  } catch {
    // Logs directory might not exist
  }

  return { messages, initialPrompt, iterationResults };
}

function parseLogEntry(entry: RawLogEntry): ConversationMessage | null {
  if (entry.type === "assistant" && entry.message?.content) {
    const content: (TextContent | ToolUseContent)[] = [];

    for (const item of entry.message.content) {
      if (item.type === "text" && item.text) {
        content.push({ type: "text", text: item.text });
      } else if (item.type === "tool_use" && item.id && item.name) {
        content.push({
          type: "tool_use",
          id: item.id,
          name: item.name,
          input: item.input || {},
        });
      }
    }

    if (content.length > 0) {
      return {
        id: entry.uuid || Math.random().toString(36),
        type: "assistant",
        timestamp: entry.timestamp,
        content,
      };
    }
  }

  if (entry.type === "user" && entry.message?.content) {
    const firstItem = entry.message.content[0];

    // Check if this is a tool result
    if (firstItem?.type === "tool_result" && firstItem.tool_use_id) {
      return {
        id: entry.uuid || Math.random().toString(36),
        type: "user",
        timestamp: entry.timestamp,
        content: [],
        toolResult: entry.tool_use_result,
        toolUseId: firstItem.tool_use_id,
      };
    }
  }

  return null;
}

export function groupIntoTurns(
  messages: ConversationMessage[]
): ConversationTurn[] {
  const turns: ConversationTurn[] = [];
  let currentTurn: ConversationTurn | null = null;
  let currentIteration = 0;
  const pendingToolCalls = new Map<string, ToolUseContent>();

  for (const msg of messages) {
    // Handle iteration boundaries
    if (msg.type === "iteration_start") {
      // Save previous turn if exists
      if (currentTurn && (currentTurn.assistant || currentTurn.toolCalls.length > 0)) {
        turns.push(currentTurn);
      }
      currentIteration = msg.iteration ?? 0;
      currentTurn = null;
      pendingToolCalls.clear();
      continue;
    }

    if (msg.type === "assistant") {
      // Check if this message has text content (start new turn)
      const hasText = msg.content.some(
        (c) => c.type === "text" && (c as TextContent).text.trim()
      );

      if (hasText) {
        // Save previous turn if exists
        if (currentTurn && (currentTurn.assistant || currentTurn.toolCalls.length > 0)) {
          turns.push(currentTurn);
        }
        currentTurn = { assistant: msg, toolCalls: [], iteration: currentIteration };
      } else if (!currentTurn) {
        currentTurn = { assistant: null, toolCalls: [], iteration: currentIteration };
      }

      // Collect tool calls
      for (const item of msg.content) {
        if (item.type === "tool_use") {
          pendingToolCalls.set((item as ToolUseContent).id, item as ToolUseContent);
        }
      }
    } else if (msg.type === "user" && msg.toolUseId && msg.toolResult !== undefined) {
      const toolCall = pendingToolCalls.get(msg.toolUseId);
      if (toolCall) {
        if (!currentTurn) {
          currentTurn = { assistant: null, toolCalls: [], iteration: currentIteration };
        }
        currentTurn.toolCalls.push({
          call: toolCall,
          result: msg.toolResult,
        });
        pendingToolCalls.delete(msg.toolUseId);
      }
    }
  }

  // Push final turn
  if (currentTurn && (currentTurn.assistant || currentTurn.toolCalls.length > 0)) {
    turns.push(currentTurn);
  }

  return turns;
}
