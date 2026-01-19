<script lang="ts">
  import {
    logsStore,
    logsLoading,
    logsError,
    logsConnected,
    clearLogs,
    startLogStreaming,
    stopLogStreaming,
  } from "../lib/stores/logs.js";
  import { workersStore } from "../lib/stores/workers.js";
  import { fetchWorkerLogs, type LogLine } from "../lib/api.js";

  let logContainer: HTMLDivElement;
  let autoScroll = $state(true);
  let levelFilter = $state<string | null>(null);
  let selectedWorker = $state<string | null>(null);
  let workerLogs = $state<LogLine[]>([]);
  let workerLogsLoading = $state(false);

  const levelColors: Record<string, string> = {
    DEBUG: "#64748b",
    INFO: "#3b82f6",
    WARN: "#eab308",
    ERROR: "#dc2626",
  };

  // Current logs based on selection
  const currentLogs = $derived(selectedWorker ? workerLogs : $logsStore);

  const filteredLogs = $derived(
    levelFilter
      ? currentLogs.filter((l) => l.level === levelFilter)
      : currentLogs
  );

  $effect(() => {
    if (autoScroll && logContainer && filteredLogs.length > 0) {
      logContainer.scrollTop = logContainer.scrollHeight;
    }
  });

  async function handleWorkerSelect(workerId: string | null) {
    selectedWorker = workerId;

    if (workerId) {
      // Stop global streaming when viewing worker logs
      stopLogStreaming();
      workerLogsLoading = true;
      try {
        const data = await fetchWorkerLogs(workerId, 1000);
        workerLogs = data.lines;
      } catch (err) {
        workerLogs = [];
      } finally {
        workerLogsLoading = false;
      }
    } else {
      // Resume global streaming
      workerLogs = [];
      startLogStreaming();
    }
  }

  async function refreshWorkerLogs() {
    if (!selectedWorker) return;
    workerLogsLoading = true;
    try {
      const data = await fetchWorkerLogs(selectedWorker, 1000);
      workerLogs = data.lines;
    } catch (err) {
      // Keep existing logs on error
    } finally {
      workerLogsLoading = false;
    }
  }

  function handleScroll() {
    if (!logContainer) return;
    const atBottom =
      logContainer.scrollHeight - logContainer.scrollTop - logContainer.clientHeight < 50;
    autoScroll = atBottom;
  }

  function handleClear() {
    if (selectedWorker) {
      workerLogs = [];
    } else {
      clearLogs();
    }
  }
</script>

<div class="log-viewer">
  <div class="toolbar">
    <div class="source-select">
      <select
        value={selectedWorker || ""}
        onchange={(e) => handleWorkerSelect(e.currentTarget.value || null)}
      >
        <option value="">Global Logs (Live)</option>
        {#if $workersStore}
          <optgroup label="Worker Logs">
            {#each $workersStore.workers as worker (worker.id)}
              <option value={worker.id}>
                {worker.taskId} - {worker.status}
              </option>
            {/each}
          </optgroup>
        {/if}
      </select>
      {#if selectedWorker}
        <button class="refresh-btn" onclick={refreshWorkerLogs} disabled={workerLogsLoading}>
          {workerLogsLoading ? "..." : "Refresh"}
        </button>
      {/if}
    </div>

    <div class="filters">
      <button
        class="filter-btn"
        class:active={levelFilter === null}
        onclick={() => (levelFilter = null)}
      >
        All
      </button>
      {#each Object.keys(levelColors) as level}
        <button
          class="filter-btn"
          class:active={levelFilter === level}
          style="--level-color: {levelColors[level]}"
          onclick={() => (levelFilter = level)}
        >
          {level}
        </button>
      {/each}
    </div>

    <div class="status">
      {#if !selectedWorker}
        <span class="connection" class:connected={$logsConnected}>
          {$logsConnected ? "Live" : "Disconnected"}
        </span>
      {:else}
        <span class="static-label">Static</span>
      {/if}
      <span class="count">{filteredLogs.length} lines</span>
      <label class="auto-scroll">
        <input type="checkbox" bind:checked={autoScroll} />
        Auto-scroll
      </label>
      <button class="clear-btn" onclick={handleClear}>Clear</button>
    </div>
  </div>

  <div class="logs" bind:this={logContainer} onscroll={handleScroll}>
    {#if ($logsLoading || workerLogsLoading) && currentLogs.length === 0}
      <div class="loading">Loading logs...</div>
    {:else if $logsError && !selectedWorker}
      <div class="error">{$logsError}</div>
    {:else if filteredLogs.length === 0}
      <div class="empty">No logs</div>
    {:else}
      {#each filteredLogs as line, i (i)}
        <div class="log-line" style="--level-color: {levelColors[line.level || ''] || '#94a3b8'}">
          {#if line.timestamp}
            <span class="timestamp">{line.timestamp}</span>
          {/if}
          {#if line.level}
            <span class="level" style="color: {levelColors[line.level]}">{line.level}</span>
          {/if}
          <span class="message">{line.message}</span>
        </div>
      {/each}
    {/if}
  </div>
</div>

<style>
  .log-viewer {
    display: flex;
    flex-direction: column;
    height: 100%;
    background: #0f172a;
    border-radius: 0.5rem;
    overflow: hidden;
  }

  .toolbar {
    display: flex;
    justify-content: space-between;
    align-items: center;
    padding: 0.5rem 1rem;
    background: #1e293b;
    border-bottom: 1px solid #334155;
    gap: 1rem;
    flex-wrap: wrap;
  }

  .source-select {
    display: flex;
    align-items: center;
    gap: 0.5rem;
  }

  .source-select select {
    padding: 0.375rem 0.5rem;
    background: #0f172a;
    color: #e2e8f0;
    border: 1px solid #334155;
    border-radius: 0.25rem;
    font-size: 0.8rem;
    cursor: pointer;
    min-width: 180px;
  }

  .source-select select:focus {
    outline: none;
    border-color: #3b82f6;
  }

  .refresh-btn {
    padding: 0.375rem 0.5rem;
    background: #334155;
    color: #e2e8f0;
    border: none;
    border-radius: 0.25rem;
    font-size: 0.75rem;
    cursor: pointer;
  }

  .refresh-btn:hover:not(:disabled) {
    background: #475569;
  }

  .refresh-btn:disabled {
    opacity: 0.5;
    cursor: not-allowed;
  }

  .filters {
    display: flex;
    gap: 0.25rem;
  }

  .filter-btn {
    padding: 0.25rem 0.5rem;
    border: 1px solid #334155;
    background: transparent;
    color: #94a3b8;
    font-size: 0.75rem;
    border-radius: 0.25rem;
    cursor: pointer;
    transition: all 0.2s;
  }

  .filter-btn:hover {
    background: #334155;
  }

  .filter-btn.active {
    background: var(--level-color, #3b82f6);
    color: white;
    border-color: var(--level-color, #3b82f6);
  }

  .status {
    display: flex;
    align-items: center;
    gap: 1rem;
    font-size: 0.75rem;
    color: #64748b;
  }

  .connection {
    display: flex;
    align-items: center;
    gap: 0.25rem;
  }

  .connection::before {
    content: "";
    width: 6px;
    height: 6px;
    border-radius: 50%;
    background: #dc2626;
  }

  .connection.connected::before {
    background: #22c55e;
    animation: pulse 2s infinite;
  }

  @keyframes pulse {
    0%, 100% { opacity: 1; }
    50% { opacity: 0.5; }
  }

  .static-label {
    color: #64748b;
    font-style: italic;
  }

  .auto-scroll {
    display: flex;
    align-items: center;
    gap: 0.25rem;
    cursor: pointer;
  }

  .auto-scroll input {
    cursor: pointer;
  }

  .clear-btn {
    padding: 0.25rem 0.5rem;
    background: #334155;
    color: #94a3b8;
    border: none;
    border-radius: 0.25rem;
    font-size: 0.75rem;
    cursor: pointer;
  }

  .clear-btn:hover {
    background: #475569;
  }

  .logs {
    flex: 1;
    overflow-y: auto;
    padding: 0.5rem;
    font-family: monospace;
    font-size: 0.8rem;
  }

  .log-line {
    padding: 0.125rem 0.5rem;
    border-left: 2px solid var(--level-color);
    margin-bottom: 0.125rem;
  }

  .log-line:hover {
    background: #1e293b;
  }

  .timestamp {
    color: #64748b;
    margin-right: 0.5rem;
  }

  .level {
    font-weight: 600;
    margin-right: 0.5rem;
    min-width: 3.5rem;
    display: inline-block;
  }

  .message {
    color: #e2e8f0;
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
</style>
