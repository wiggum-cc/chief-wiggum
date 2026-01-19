<script lang="ts">
  import { workersStore } from "../lib/stores/workers.js";
  import { startRun, stopAll } from "../lib/api.js";

  let loading = $state(false);
  let message = $state<string | null>(null);

  async function handleStart() {
    loading = true;
    message = null;
    try {
      const result = await startRun();
      message = result.message;
      setTimeout(() => (message = null), 3000);
    } catch (err) {
      message = err instanceof Error ? err.message : "Failed to start";
    } finally {
      loading = false;
    }
  }

  async function handleStop() {
    loading = true;
    message = null;
    try {
      const result = await stopAll(true);
      message = result.message;
      setTimeout(() => (message = null), 3000);
    } catch (err) {
      message = err instanceof Error ? err.message : "Failed to stop";
    } finally {
      loading = false;
    }
  }
</script>

<header class="header">
  <div class="title">
    <h1>Chief Wiggum</h1>
    <span class="subtitle">Worker Dashboard</span>
  </div>

  <div class="status">
    {#if $workersStore}
      <span class="status-item">
        <span class="dot" class:running={$workersStore.orchestrator.running}></span>
        Orchestrator: {$workersStore.orchestrator.running ? "Running" : "Stopped"}
      </span>
      <span class="status-item">
        Workers: {$workersStore.counts.running} / {$workersStore.counts.total}
      </span>
    {/if}
  </div>

  <div class="actions">
    {#if message}
      <span class="message">{message}</span>
    {/if}
    <button class="btn btn-primary" onclick={handleStart} disabled={loading}>
      Start Run
    </button>
    <button class="btn btn-danger" onclick={handleStop} disabled={loading}>
      Stop All
    </button>
  </div>
</header>

<style>
  .header {
    display: flex;
    align-items: center;
    justify-content: space-between;
    padding: 1rem 1.5rem;
    background: #1e293b;
    border-bottom: 1px solid #334155;
  }

  .title h1 {
    font-size: 1.25rem;
    font-weight: 600;
    color: #f1f5f9;
    margin: 0;
  }

  .subtitle {
    font-size: 0.75rem;
    color: #64748b;
  }

  .status {
    display: flex;
    gap: 1.5rem;
  }

  .status-item {
    display: flex;
    align-items: center;
    gap: 0.5rem;
    font-size: 0.85rem;
    color: #94a3b8;
  }

  .dot {
    width: 8px;
    height: 8px;
    border-radius: 50%;
    background: #64748b;
  }

  .dot.running {
    background: #22c55e;
    box-shadow: 0 0 8px #22c55e80;
  }

  .actions {
    display: flex;
    gap: 0.75rem;
    align-items: center;
  }

  .message {
    font-size: 0.8rem;
    color: #94a3b8;
    max-width: 200px;
    overflow: hidden;
    text-overflow: ellipsis;
    white-space: nowrap;
  }

  .btn {
    padding: 0.5rem 1rem;
    border: none;
    border-radius: 0.375rem;
    font-size: 0.85rem;
    font-weight: 500;
    cursor: pointer;
    transition: all 0.2s;
  }

  .btn:disabled {
    opacity: 0.5;
    cursor: not-allowed;
  }

  .btn-primary {
    background: #3b82f6;
    color: white;
  }

  .btn-primary:hover:not(:disabled) {
    background: #2563eb;
  }

  .btn-danger {
    background: #dc2626;
    color: white;
  }

  .btn-danger:hover:not(:disabled) {
    background: #b91c1c;
  }
</style>
