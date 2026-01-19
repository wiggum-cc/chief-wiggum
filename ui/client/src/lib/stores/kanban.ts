import { writable } from "svelte/store";
import type { Task, KanbanResponse } from "../api.js";
import { fetchKanban } from "../api.js";

export const kanbanStore = writable<KanbanResponse | null>(null);
export const kanbanLoading = writable(false);
export const kanbanError = writable<string | null>(null);

export async function refreshKanban(): Promise<void> {
  kanbanLoading.set(true);
  kanbanError.set(null);

  try {
    const data = await fetchKanban();
    kanbanStore.set(data);
  } catch (err) {
    kanbanError.set(err instanceof Error ? err.message : "Unknown error");
  } finally {
    kanbanLoading.set(false);
  }
}

let pollInterval: ReturnType<typeof setInterval> | null = null;

export function startKanbanPolling(intervalMs = 5000): void {
  if (pollInterval) return;
  refreshKanban();
  pollInterval = setInterval(refreshKanban, intervalMs);
}

export function stopKanbanPolling(): void {
  if (pollInterval) {
    clearInterval(pollInterval);
    pollInterval = null;
  }
}
