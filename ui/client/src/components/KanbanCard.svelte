<script lang="ts">
  import type { Task } from "../lib/api.js";

  let { task }: { task: Task } = $props();
  let expanded = $state(false);

  const priorityColors: Record<string, string> = {
    CRITICAL: "#dc2626",
    HIGH: "#f97316",
    MEDIUM: "#eab308",
    LOW: "#22c55e",
  };
</script>

<div
  class="card"
  class:expanded
  role="button"
  tabindex="0"
  onclick={() => (expanded = !expanded)}
  onkeydown={(e) => e.key === "Enter" && (expanded = !expanded)}
>
  <div class="card-header">
    <span class="task-id">{task.id}</span>
    <span
      class="priority"
      style="background: {priorityColors[task.priority] || '#64748b'}"
    >
      {task.priority}
    </span>
  </div>

  <div class="title">{task.title || task.description || "No description"}</div>

  {#if task.dependencies.length > 0}
    <div class="deps">
      Deps: {task.dependencies.join(", ")}
    </div>
  {/if}

  {#if expanded}
    <div class="details">
      {#if task.description}
        <div class="detail-section">
          <strong>Description:</strong>
          <p>{task.description}</p>
        </div>
      {/if}

      {#if task.scope.length > 0}
        <div class="detail-section">
          <strong>Scope:</strong>
          <ul>
            {#each task.scope as item}
              <li>{item}</li>
            {/each}
          </ul>
        </div>
      {/if}

      {#if task.acceptanceCriteria.length > 0}
        <div class="detail-section">
          <strong>Acceptance Criteria:</strong>
          <ul>
            {#each task.acceptanceCriteria as item}
              <li>{item}</li>
            {/each}
          </ul>
        </div>
      {/if}
    </div>
  {/if}
</div>

<style>
  .card {
    background: #0f172a;
    border-radius: 0.375rem;
    padding: 0.75rem;
    cursor: pointer;
    border: 1px solid #334155;
    transition: all 0.2s;
  }

  .card:hover {
    border-color: #475569;
  }

  .card.expanded {
    border-color: #3b82f6;
  }

  .card-header {
    display: flex;
    justify-content: space-between;
    align-items: center;
    margin-bottom: 0.5rem;
  }

  .task-id {
    font-family: monospace;
    font-size: 0.75rem;
    color: #3b82f6;
    font-weight: 600;
  }

  .priority {
    font-size: 0.65rem;
    padding: 0.125rem 0.375rem;
    border-radius: 0.25rem;
    color: white;
    font-weight: 600;
    text-transform: uppercase;
  }

  .title {
    font-size: 0.85rem;
    color: #e2e8f0;
    line-height: 1.4;
  }

  .deps {
    font-size: 0.7rem;
    color: #64748b;
    margin-top: 0.5rem;
    font-family: monospace;
  }

  .details {
    margin-top: 0.75rem;
    padding-top: 0.75rem;
    border-top: 1px solid #334155;
  }

  .detail-section {
    margin-bottom: 0.5rem;
  }

  .detail-section strong {
    font-size: 0.75rem;
    color: #94a3b8;
    display: block;
    margin-bottom: 0.25rem;
  }

  .detail-section p {
    font-size: 0.8rem;
    color: #cbd5e1;
    margin: 0;
  }

  .detail-section ul {
    margin: 0;
    padding-left: 1rem;
    font-size: 0.8rem;
    color: #cbd5e1;
  }

  .detail-section li {
    margin-bottom: 0.125rem;
  }
</style>
