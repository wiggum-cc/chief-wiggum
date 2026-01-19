<script lang="ts">
  import {
    fetchConversation,
    type ConversationTurn,
    type ToolUseContent,
    type InitialPrompt,
    type IterationResult,
  } from "../lib/api.js";

  let { workerId }: { workerId: string } = $props();

  let turns = $state<ConversationTurn[]>([]);
  let initialPrompt = $state<InitialPrompt | null>(null);
  let iterationResults = $state<IterationResult[]>([]);
  let loading = $state(false);
  let error = $state<string | null>(null);
  let expandedResults = $state<Set<string>>(new Set());
  let showSystemPrompt = $state(false);
  let showUserPrompt = $state(false);
  let collapsedIterations = $state<Set<number>>(new Set());

  $effect(() => {
    if (workerId) {
      loadConversation();
    }
  });

  async function loadConversation() {
    loading = true;
    error = null;
    try {
      const data = await fetchConversation(workerId);
      turns = data.turns;
      initialPrompt = data.initialPrompt;
      iterationResults = data.iterationResults;
    } catch (err) {
      error = err instanceof Error ? err.message : "Failed to load";
      turns = [];
      initialPrompt = null;
      iterationResults = [];
    } finally {
      loading = false;
    }
  }

  function formatJson(obj: unknown): string {
    if (typeof obj === "string") return obj;
    return JSON.stringify(obj, null, 2);
  }

  function truncate(text: string, max = 100): string {
    if (text.length <= max) return text;
    return text.slice(0, max) + "...";
  }

  function getToolPreview(call: ToolUseContent): string {
    const input = call.input;
    if (call.name === "Read" && input.file_path) return String(input.file_path);
    if (call.name === "Write" && input.file_path) return String(input.file_path);
    if (call.name === "Edit" && input.file_path) return String(input.file_path);
    if (call.name === "Bash" && input.command) return String(input.command).slice(0, 60);
    if (call.name === "Glob" && input.pattern) return String(input.pattern);
    if (call.name === "Grep" && input.pattern) return String(input.pattern);
    if (call.name === "Task" && input.description) return String(input.description);
    if (call.name === "TodoWrite") return "Update todos";
    return "";
  }

  function toggleResult(id: string) {
    if (expandedResults.has(id)) {
      expandedResults.delete(id);
    } else {
      expandedResults.add(id);
    }
    expandedResults = new Set(expandedResults);
  }

  function toggleIteration(iter: number) {
    if (collapsedIterations.has(iter)) {
      collapsedIterations.delete(iter);
    } else {
      collapsedIterations.add(iter);
    }
    collapsedIterations = new Set(collapsedIterations);
  }

  function formatDuration(ms: number): string {
    if (ms < 1000) return `${ms}ms`;
    if (ms < 60000) return `${(ms / 1000).toFixed(1)}s`;
    return `${(ms / 60000).toFixed(1)}m`;
  }

  function formatCost(usd: number): string {
    return `$${usd.toFixed(4)}`;
  }

  function getIterationResult(iter: number): IterationResult | undefined {
    return iterationResults.find(r => r.iteration === iter);
  }

  function getTurnsByIteration(iter: number): ConversationTurn[] {
    return turns.filter(t => t.iteration === iter);
  }

  // Get unique iterations
  const iterations = $derived([...new Set(turns.map(t => t.iteration ?? 0))].sort((a, b) => a - b));
</script>

<div class="conversation">
  {#if loading}
    <div class="loading">Loading conversation...</div>
  {:else if error}
    <div class="error">{error}</div>
  {:else if turns.length === 0 && !initialPrompt}
    <div class="empty">No conversation data</div>
  {:else}
    <div class="turns">
      {#if initialPrompt}
        <div class="initial-prompts">
          <div class="prompt-block">
            <div
              class="prompt-header"
              role="button"
              tabindex="0"
              onclick={() => (showSystemPrompt = !showSystemPrompt)}
              onkeydown={(e) => e.key === "Enter" && (showSystemPrompt = !showSystemPrompt)}
            >
              <span class="prompt-icon">{showSystemPrompt ? "▼" : "▶"}</span>
              <span class="prompt-label system">System Prompt</span>
              <span class="prompt-size">{initialPrompt.systemPrompt.length} chars</span>
            </div>
            {#if showSystemPrompt}
              <pre class="prompt-content">{initialPrompt.systemPrompt}</pre>
            {/if}
          </div>
          <div class="prompt-block">
            <div
              class="prompt-header"
              role="button"
              tabindex="0"
              onclick={() => (showUserPrompt = !showUserPrompt)}
              onkeydown={(e) => e.key === "Enter" && (showUserPrompt = !showUserPrompt)}
            >
              <span class="prompt-icon">{showUserPrompt ? "▼" : "▶"}</span>
              <span class="prompt-label user">User Prompt</span>
              <span class="prompt-size">{initialPrompt.userPrompt.length} chars</span>
            </div>
            {#if showUserPrompt}
              <pre class="prompt-content">{initialPrompt.userPrompt}</pre>
            {/if}
          </div>
        </div>
      {/if}

      {#each iterations as iter (iter)}
        {@const result = getIterationResult(iter)}
        {@const iterTurns = getTurnsByIteration(iter)}
        {@const isCollapsed = collapsedIterations.has(iter)}

        <div class="iteration-block">
          <div
            class="iteration-header"
            role="button"
            tabindex="0"
            onclick={() => toggleIteration(iter)}
            onkeydown={(e) => e.key === "Enter" && toggleIteration(iter)}
          >
            <span class="iter-icon">{isCollapsed ? "▶" : "▼"}</span>
            <span class="iter-title">Iteration {iter}</span>
            <span class="iter-stats">
              {iterTurns.length} turns
              {#if result}
                <span class="iter-separator">|</span>
                <span class="iter-duration">{formatDuration(result.durationMs)}</span>
                <span class="iter-separator">|</span>
                <span class="iter-cost">{formatCost(result.totalCostUsd)}</span>
                <span class="iter-separator">|</span>
                <span class="iter-status" class:error={result.isError}>
                  {result.subtype}
                </span>
              {/if}
            </span>
          </div>

          {#if !isCollapsed}
            {#if result}
              <div class="iteration-metrics">
                <span class="metric">
                  <span class="metric-label">Turns:</span> {result.numTurns}
                </span>
                <span class="metric">
                  <span class="metric-label">Duration:</span> {formatDuration(result.durationMs)}
                </span>
                <span class="metric">
                  <span class="metric-label">API Time:</span> {formatDuration(result.durationApiMs)}
                </span>
                <span class="metric">
                  <span class="metric-label">Cost:</span> {formatCost(result.totalCostUsd)}
                </span>
                <span class="metric">
                  <span class="metric-label">Input:</span> {result.usage.inputTokens.toLocaleString()}
                </span>
                <span class="metric">
                  <span class="metric-label">Output:</span> {result.usage.outputTokens.toLocaleString()}
                </span>
                <span class="metric">
                  <span class="metric-label">Cache Read:</span> {result.usage.cacheReadInputTokens.toLocaleString()}
                </span>
              </div>
            {/if}

            <div class="iteration-turns">
              {#each iterTurns as turn, turnIndex (turnIndex)}
                <div class="turn">
                  {#if turn.assistant}
                    {#each turn.assistant.content as content}
                      {#if content.type === "text" && content.text.trim()}
                        <div class="message assistant">
                          <div class="message-header">
                            <span class="role">Assistant</span>
                          </div>
                          <div class="message-content">
                            <pre>{content.text}</pre>
                          </div>
                        </div>
                      {/if}
                    {/each}
                  {/if}

                  {#each turn.toolCalls as toolCall (toolCall.call.id)}
                    {@const resultStr = formatJson(toolCall.result)}
                    {@const isExpanded = expandedResults.has(toolCall.call.id)}
                    <div class="tool-call">
                      <div
                        class="tool-header"
                        role="button"
                        tabindex="0"
                        onclick={() => toggleResult(toolCall.call.id)}
                        onkeydown={(e) => e.key === "Enter" && toggleResult(toolCall.call.id)}
                      >
                        <span class="tool-icon">{isExpanded ? "▼" : "▶"}</span>
                        <span class="tool-name">{toolCall.call.name}</span>
                        <span class="tool-preview">{truncate(getToolPreview(toolCall.call), 50)}</span>
                      </div>
                      {#if isExpanded}
                        <div class="tool-body">
                          <div class="tool-section">
                            <div class="section-label">Input</div>
                            <pre class="section-content">{formatJson(toolCall.call.input)}</pre>
                          </div>
                          <div class="tool-section">
                            <div class="section-label">Result ({resultStr.length} chars)</div>
                            <pre class="section-content">{resultStr}</pre>
                          </div>
                        </div>
                      {/if}
                    </div>
                  {/each}
                </div>
              {/each}
            </div>
          {/if}
        </div>
      {/each}
    </div>
  {/if}
</div>

<style>
  .conversation {
    height: 100%;
    overflow-y: auto;
    padding: 1rem;
  }

  .loading,
  .error,
  .empty {
    padding: 2rem;
    text-align: center;
    color: #64748b;
  }

  .error {
    color: #f87171;
  }

  .turns {
    display: flex;
    flex-direction: column;
    gap: 0.75rem;
  }

  .turn {
    display: flex;
    flex-direction: column;
    gap: 0.5rem;
  }

  .message {
    background: #1e293b;
    border-radius: 0.5rem;
    overflow: hidden;
  }

  .message-header {
    padding: 0.5rem 0.75rem;
    background: #0f172a;
    border-bottom: 1px solid #334155;
  }

  .role {
    font-size: 0.75rem;
    font-weight: 600;
    color: #3b82f6;
    text-transform: uppercase;
  }

  .message-content {
    padding: 0.75rem;
  }

  .message-content pre {
    margin: 0;
    white-space: pre-wrap;
    word-break: break-word;
    font-family: inherit;
    font-size: 0.85rem;
    color: #e2e8f0;
    line-height: 1.5;
  }

  .tool-call {
    background: #1a1f2e;
    border: 1px solid #334155;
    border-radius: 0.375rem;
    overflow: hidden;
  }

  .tool-header {
    display: flex;
    align-items: center;
    gap: 0.5rem;
    padding: 0.5rem 0.75rem;
    cursor: pointer;
    user-select: none;
    background: #0f172a;
  }

  .tool-header:hover {
    background: #1e293b;
  }

  .tool-icon {
    color: #64748b;
    font-size: 0.7rem;
    width: 1rem;
  }

  .tool-name {
    font-family: monospace;
    font-size: 0.8rem;
    font-weight: 600;
    color: #f59e0b;
  }

  .tool-preview {
    font-size: 0.75rem;
    color: #64748b;
    font-family: monospace;
    overflow: hidden;
    text-overflow: ellipsis;
    white-space: nowrap;
    flex: 1;
  }

  .tool-body {
    border-top: 1px solid #334155;
  }

  .tool-section {
    border-bottom: 1px solid #334155;
  }

  .tool-section:last-child {
    border-bottom: none;
  }

  .section-label {
    padding: 0.375rem 0.75rem;
    font-size: 0.7rem;
    font-weight: 600;
    color: #64748b;
    text-transform: uppercase;
    background: #0f172a;
  }

  .section-content {
    margin: 0;
    padding: 0.75rem;
    background: #0f172a;
    font-family: monospace;
    font-size: 0.75rem;
    color: #cbd5e1;
    white-space: pre-wrap;
    word-break: break-word;
    max-height: 300px;
    overflow-y: auto;
  }

  .initial-prompts {
    display: flex;
    flex-direction: column;
    gap: 0.5rem;
    margin-bottom: 1rem;
  }

  .prompt-block {
    background: #1e293b;
    border: 1px solid #334155;
    border-radius: 0.375rem;
    overflow: hidden;
  }

  .prompt-header {
    display: flex;
    align-items: center;
    gap: 0.5rem;
    padding: 0.5rem 0.75rem;
    cursor: pointer;
    user-select: none;
    background: #0f172a;
  }

  .prompt-header:hover {
    background: #1e293b;
  }

  .prompt-icon {
    color: #64748b;
    font-size: 0.7rem;
    width: 1rem;
  }

  .prompt-label {
    font-size: 0.8rem;
    font-weight: 600;
    text-transform: uppercase;
  }

  .prompt-label.system {
    color: #a855f7;
  }

  .prompt-label.user {
    color: #22c55e;
  }

  .prompt-size {
    font-size: 0.7rem;
    color: #64748b;
    margin-left: auto;
  }

  .prompt-content {
    margin: 0;
    padding: 0.75rem;
    background: #0f172a;
    font-family: monospace;
    font-size: 0.75rem;
    color: #cbd5e1;
    white-space: pre-wrap;
    word-break: break-word;
    max-height: 400px;
    overflow-y: auto;
    border-top: 1px solid #334155;
  }

  .iteration-block {
    border: 1px solid #334155;
    border-radius: 0.5rem;
    overflow: hidden;
    background: #0f172a;
  }

  .iteration-header {
    display: flex;
    align-items: center;
    gap: 0.75rem;
    padding: 0.75rem 1rem;
    cursor: pointer;
    user-select: none;
    background: #1e293b;
    border-bottom: 1px solid #334155;
  }

  .iteration-header:hover {
    background: #334155;
  }

  .iter-icon {
    color: #f59e0b;
    font-size: 0.7rem;
  }

  .iter-title {
    font-weight: 600;
    color: #f59e0b;
    font-size: 0.9rem;
  }

  .iter-stats {
    margin-left: auto;
    font-size: 0.75rem;
    color: #64748b;
    display: flex;
    align-items: center;
    gap: 0.5rem;
  }

  .iter-separator {
    color: #475569;
  }

  .iter-duration {
    color: #3b82f6;
  }

  .iter-cost {
    color: #22c55e;
  }

  .iter-status {
    color: #94a3b8;
  }

  .iter-status.error {
    color: #f87171;
  }

  .iteration-metrics {
    display: flex;
    flex-wrap: wrap;
    gap: 1rem;
    padding: 0.5rem 1rem;
    background: #1a1f2e;
    border-bottom: 1px solid #334155;
  }

  .metric {
    font-size: 0.75rem;
    color: #e2e8f0;
  }

  .metric-label {
    color: #64748b;
  }

  .iteration-turns {
    padding: 0.75rem;
    display: flex;
    flex-direction: column;
    gap: 0.5rem;
  }
</style>
