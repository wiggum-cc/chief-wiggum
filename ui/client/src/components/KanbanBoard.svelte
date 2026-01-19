<script lang="ts">
  import { kanbanStore, kanbanLoading, kanbanError } from "../lib/stores/kanban.js";
  import KanbanCard from "./KanbanCard.svelte";

  const columns = [
    { key: "pending", label: "Pending", color: "#64748b" },
    { key: "in_progress", label: "In Progress", color: "#3b82f6" },
    { key: "complete", label: "Complete", color: "#22c55e" },
    { key: "failed", label: "Failed", color: "#dc2626" },
  ] as const;
</script>

<div class="board">
  {#if $kanbanLoading && !$kanbanStore}
    <div class="loading">Loading kanban...</div>
  {:else if $kanbanError}
    <div class="error">{$kanbanError}</div>
  {:else if $kanbanStore}
    {#each columns as column}
      <div class="column">
        <div class="column-header" style="border-color: {column.color}">
          <span class="column-title">{column.label}</span>
          <span class="column-count">{$kanbanStore.grouped[column.key]?.length || 0}</span>
        </div>
        <div class="column-content">
          {#each $kanbanStore.grouped[column.key] || [] as task (task.id)}
            <KanbanCard {task} />
          {/each}
          {#if !$kanbanStore.grouped[column.key]?.length}
            <div class="empty">No tasks</div>
          {/if}
        </div>
      </div>
    {/each}
  {:else}
    <div class="empty">No kanban data</div>
  {/if}
</div>

<style>
  .board {
    display: grid;
    grid-template-columns: repeat(4, 1fr);
    gap: 1rem;
    height: 100%;
    min-height: 0;
  }

  .column {
    display: flex;
    flex-direction: column;
    background: #1e293b;
    border-radius: 0.5rem;
    overflow: hidden;
  }

  .column-header {
    display: flex;
    justify-content: space-between;
    align-items: center;
    padding: 0.75rem 1rem;
    background: #0f172a;
    border-left: 3px solid;
  }

  .column-title {
    font-weight: 600;
    font-size: 0.9rem;
    color: #e2e8f0;
  }

  .column-count {
    background: #334155;
    color: #94a3b8;
    padding: 0.125rem 0.5rem;
    border-radius: 1rem;
    font-size: 0.75rem;
  }

  .column-content {
    flex: 1;
    overflow-y: auto;
    padding: 0.5rem;
    display: flex;
    flex-direction: column;
    gap: 0.5rem;
  }

  .loading,
  .error,
  .empty {
    padding: 2rem;
    text-align: center;
    color: #64748b;
    font-size: 0.9rem;
  }

  .error {
    color: #f87171;
  }
</style>
