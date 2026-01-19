<script lang="ts">
  import { onMount, onDestroy } from "svelte";
  import Header from "./components/Header.svelte";
  import KanbanBoard from "./components/KanbanBoard.svelte";
  import WorkersList from "./components/WorkersList.svelte";
  import LogViewer from "./components/LogViewer.svelte";
  import ConversationView from "./components/ConversationView.svelte";
  import { startKanbanPolling, stopKanbanPolling } from "./lib/stores/kanban.js";
  import { startWorkersPolling, stopWorkersPolling } from "./lib/stores/workers.js";
  import { startLogStreaming, stopLogStreaming } from "./lib/stores/logs.js";

  let activeTab = $state<"kanban" | "workers" | "logs">("kanban");
  let selectedWorkerId = $state<string | null>(null);

  function handleViewConversation(workerId: string) {
    selectedWorkerId = workerId;
  }

  function closeConversation() {
    selectedWorkerId = null;
  }

  onMount(() => {
    startKanbanPolling();
    startWorkersPolling();
    startLogStreaming();
  });

  onDestroy(() => {
    stopKanbanPolling();
    stopWorkersPolling();
    stopLogStreaming();
  });
</script>

<div class="app">
  <Header />

  <nav class="tabs">
    <button
      class="tab"
      class:active={activeTab === "kanban"}
      onclick={() => (activeTab = "kanban")}
    >
      Kanban
    </button>
    <button
      class="tab"
      class:active={activeTab === "workers"}
      onclick={() => (activeTab = "workers")}
    >
      Workers
    </button>
    <button
      class="tab"
      class:active={activeTab === "logs"}
      onclick={() => (activeTab = "logs")}
    >
      Logs
    </button>
  </nav>

  <main class="content">
    {#if selectedWorkerId}
      <div class="conversation-panel">
        <div class="panel-header">
          <span class="panel-title">Conversation: {selectedWorkerId}</span>
          <button class="close-btn" onclick={closeConversation}>Close</button>
        </div>
        <div class="panel-content">
          <ConversationView workerId={selectedWorkerId} />
        </div>
      </div>
    {:else if activeTab === "kanban"}
      <KanbanBoard />
    {:else if activeTab === "workers"}
      <WorkersList onViewConversation={handleViewConversation} />
    {:else if activeTab === "logs"}
      <LogViewer />
    {/if}
  </main>
</div>

<style>
  .app {
    display: flex;
    flex-direction: column;
    height: 100vh;
  }

  .tabs {
    display: flex;
    gap: 0;
    padding: 0 1rem;
    background: #1e293b;
    border-bottom: 1px solid #334155;
  }

  .tab {
    padding: 0.75rem 1.5rem;
    border: none;
    background: transparent;
    color: #94a3b8;
    font-size: 0.9rem;
    cursor: pointer;
    border-bottom: 2px solid transparent;
    transition: all 0.2s;
  }

  .tab:hover {
    color: #e2e8f0;
    background: #334155;
  }

  .tab.active {
    color: #3b82f6;
    border-bottom-color: #3b82f6;
  }

  .content {
    flex: 1;
    overflow: auto;
    padding: 1rem;
  }

  .conversation-panel {
    display: flex;
    flex-direction: column;
    height: 100%;
    background: #0f172a;
    border-radius: 0.5rem;
    overflow: hidden;
  }

  .panel-header {
    display: flex;
    justify-content: space-between;
    align-items: center;
    padding: 0.75rem 1rem;
    background: #1e293b;
    border-bottom: 1px solid #334155;
  }

  .panel-title {
    font-size: 0.9rem;
    font-weight: 600;
    color: #e2e8f0;
    font-family: monospace;
  }

  .close-btn {
    padding: 0.375rem 0.75rem;
    background: #334155;
    color: #e2e8f0;
    border: none;
    border-radius: 0.25rem;
    font-size: 0.8rem;
    cursor: pointer;
  }

  .close-btn:hover {
    background: #475569;
  }

  .panel-content {
    flex: 1;
    overflow: hidden;
  }
</style>
