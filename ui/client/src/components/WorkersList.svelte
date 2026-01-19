<script lang="ts">
  import { workersStore, workersLoading, workersError } from "../lib/stores/workers.js";
  import { stopWorker } from "../lib/api.js";
  import type { Worker } from "../lib/api.js";

  let { onViewConversation }: { onViewConversation?: (workerId: string) => void } = $props();

  let stoppingWorker = $state<string | null>(null);

  async function handleStop(worker: Worker) {
    if (!confirm(`Stop worker ${worker.id}?`)) return;

    stoppingWorker = worker.id;
    try {
      await stopWorker(worker.id);
    } catch (err) {
      alert(err instanceof Error ? err.message : "Failed to stop worker");
    } finally {
      stoppingWorker = null;
    }
  }

  function formatTime(timestamp: number): string {
    const date = new Date(timestamp * 1000);
    return date.toLocaleString();
  }

  const statusColors: Record<string, string> = {
    running: "#22c55e",
    stopped: "#64748b",
    completed: "#3b82f6",
    failed: "#dc2626",
  };
</script>

<div class="workers">
  {#if $workersLoading && !$workersStore}
    <div class="loading">Loading workers...</div>
  {:else if $workersError}
    <div class="error">{$workersError}</div>
  {:else if $workersStore && $workersStore.workers.length > 0}
    <table class="table">
      <thead>
        <tr>
          <th>Worker ID</th>
          <th>Task</th>
          <th>Status</th>
          <th>PID</th>
          <th>Started</th>
          <th>PR</th>
          <th>Actions</th>
        </tr>
      </thead>
      <tbody>
        {#each $workersStore.workers as worker (worker.id)}
          <tr>
            <td class="mono">{worker.id}</td>
            <td class="mono task-id">{worker.taskId}</td>
            <td>
              <span
                class="status-badge"
                style="background: {statusColors[worker.status]}"
              >
                {worker.status}
              </span>
            </td>
            <td class="mono">{worker.pid || "-"}</td>
            <td class="time">{formatTime(worker.timestamp)}</td>
            <td>
              {#if worker.prUrl}
                <a href={worker.prUrl} target="_blank" rel="noopener">View PR</a>
              {:else}
                -
              {/if}
            </td>
            <td class="actions">
              <button
                class="btn-conv"
                onclick={() => onViewConversation?.(worker.id)}
              >
                Chat
              </button>
              {#if worker.status === "running"}
                <button
                  class="btn-stop"
                  onclick={() => handleStop(worker)}
                  disabled={stoppingWorker === worker.id}
                >
                  {stoppingWorker === worker.id ? "..." : "Stop"}
                </button>
              {/if}
            </td>
          </tr>
        {/each}
      </tbody>
    </table>
  {:else}
    <div class="empty">No workers found</div>
  {/if}
</div>

<style>
  .workers {
    height: 100%;
    overflow: auto;
  }

  .table {
    width: 100%;
    border-collapse: collapse;
    font-size: 0.85rem;
  }

  .table th,
  .table td {
    padding: 0.75rem 1rem;
    text-align: left;
    border-bottom: 1px solid #334155;
  }

  .table th {
    background: #1e293b;
    color: #94a3b8;
    font-weight: 600;
    font-size: 0.75rem;
    text-transform: uppercase;
    letter-spacing: 0.05em;
    position: sticky;
    top: 0;
  }

  .table tbody tr:hover {
    background: #1e293b40;
  }

  .mono {
    font-family: monospace;
  }

  .task-id {
    color: #3b82f6;
  }

  .time {
    font-size: 0.8rem;
    color: #64748b;
  }

  .status-badge {
    display: inline-block;
    padding: 0.125rem 0.5rem;
    border-radius: 1rem;
    font-size: 0.7rem;
    font-weight: 600;
    color: white;
    text-transform: uppercase;
  }

  .actions {
    display: flex;
    gap: 0.375rem;
  }

  .btn-conv {
    padding: 0.25rem 0.5rem;
    background: #3b82f6;
    color: white;
    border: none;
    border-radius: 0.25rem;
    font-size: 0.75rem;
    cursor: pointer;
    transition: background 0.2s;
  }

  .btn-conv:hover {
    background: #2563eb;
  }

  .btn-stop {
    padding: 0.25rem 0.5rem;
    background: #dc2626;
    color: white;
    border: none;
    border-radius: 0.25rem;
    font-size: 0.75rem;
    cursor: pointer;
    transition: background 0.2s;
  }

  .btn-stop:hover:not(:disabled) {
    background: #b91c1c;
  }

  .btn-stop:disabled {
    opacity: 0.5;
    cursor: not-allowed;
  }

  a {
    color: #3b82f6;
    text-decoration: none;
  }

  a:hover {
    text-decoration: underline;
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
