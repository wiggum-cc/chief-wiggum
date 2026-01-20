const BASE_URL = "/api";

export interface Task {
  id: string;
  title: string;
  status: "pending" | "in_progress" | "complete" | "failed";
  description: string;
  priority: "CRITICAL" | "HIGH" | "MEDIUM" | "LOW";
  dependencies: string[];
  scope: string[];
  outOfScope: string[];
  acceptanceCriteria: string[];
}

export interface Worker {
  id: string;
  taskId: string;
  timestamp: number;
  pid: number | null;
  status: "running" | "stopped" | "completed" | "failed";
  prdPath: string;
  logPath: string;
  workspacePath: string;
  prUrl: string | null;
}

export interface LogLine {
  raw: string;
  timestamp: string | null;
  level: string | null;
  message: string;
}

export interface KanbanResponse {
  tasks: Task[];
  grouped: Record<string, Task[]>;
  counts: {
    pending: number;
    in_progress: number;
    complete: number;
    failed: number;
    total: number;
  };
}

export interface WorkersResponse {
  workers: Worker[];
  orchestrator: { running: boolean; pid: number | null };
  counts: {
    running: number;
    stopped: number;
    completed: number;
    failed: number;
    total: number;
  };
}

export interface LogsResponse {
  lines: LogLine[];
  path: string;
}

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

export interface ConversationMessage {
  id: string;
  type: "assistant" | "user" | "system" | "iteration_start";
  timestamp?: string;
  content: (TextContent | ToolUseContent)[];
  toolResult?: unknown;
  parentToolUseId?: string;
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

export interface ContextUsage {
  tokens: number;
  size: number;
  percent: number;
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
  context?: ContextUsage;
}

export interface ConversationResponse {
  messages: ConversationMessage[];
  turns: ConversationTurn[];
  initialPrompt: InitialPrompt | null;
  iterationResults: IterationResult[];
  messageCount: number;
  turnCount: number;
}

export async function fetchKanban(): Promise<KanbanResponse> {
  const res = await fetch(`${BASE_URL}/kanban`);
  if (!res.ok) throw new Error("Failed to fetch kanban");
  return res.json();
}

export async function fetchWorkers(): Promise<WorkersResponse> {
  const res = await fetch(`${BASE_URL}/workers`);
  if (!res.ok) throw new Error("Failed to fetch workers");
  return res.json();
}

export async function fetchLogs(
  type: "combined" | "audit" = "combined",
  lines = 500
): Promise<LogsResponse> {
  const res = await fetch(`${BASE_URL}/logs/${type}?lines=${lines}`);
  if (!res.ok) throw new Error("Failed to fetch logs");
  return res.json();
}

export async function fetchWorkerLogs(
  workerId: string,
  lines = 500
): Promise<LogsResponse> {
  const res = await fetch(`${BASE_URL}/logs/worker/${workerId}?lines=${lines}`);
  if (!res.ok) throw new Error("Failed to fetch worker logs");
  return res.json();
}

export async function startRun(
  maxWorkers?: number
): Promise<{ success: boolean; message: string }> {
  const res = await fetch(`${BASE_URL}/run`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ maxWorkers }),
  });
  return res.json();
}

export async function stopAll(
  orchestrator = false
): Promise<{ success: boolean; message: string }> {
  const res = await fetch(`${BASE_URL}/stop`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ orchestrator }),
  });
  return res.json();
}

export async function stopWorker(
  workerId: string
): Promise<{ success: boolean; message: string }> {
  const res = await fetch(`${BASE_URL}/workers/${workerId}/stop`, {
    method: "POST",
  });
  return res.json();
}

export async function fetchConversation(
  workerId: string
): Promise<ConversationResponse> {
  const res = await fetch(`${BASE_URL}/conversation/${workerId}`);
  if (!res.ok) throw new Error("Failed to fetch conversation");
  return res.json();
}

export function subscribeToLogs(
  onLog: (line: LogLine) => void,
  onError?: (error: Event) => void
): EventSource {
  const es = new EventSource(`${BASE_URL}/logs/stream`);

  es.addEventListener("log", (event) => {
    const line = JSON.parse(event.data);
    onLog(line);
  });

  es.onerror = (error) => {
    if (onError) onError(error);
  };

  return es;
}
