import { writable } from "svelte/store";
import type { WorkersResponse } from "../api.js";
import { fetchWorkers } from "../api.js";

export const workersStore = writable<WorkersResponse | null>(null);
export const workersLoading = writable(false);
export const workersError = writable<string | null>(null);

export async function refreshWorkers(): Promise<void> {
  workersLoading.set(true);
  workersError.set(null);

  try {
    const data = await fetchWorkers();
    workersStore.set(data);
  } catch (err) {
    workersError.set(err instanceof Error ? err.message : "Unknown error");
  } finally {
    workersLoading.set(false);
  }
}

let pollInterval: ReturnType<typeof setInterval> | null = null;

export function startWorkersPolling(intervalMs = 2000): void {
  if (pollInterval) return;
  refreshWorkers();
  pollInterval = setInterval(refreshWorkers, intervalMs);
}

export function stopWorkersPolling(): void {
  if (pollInterval) {
    clearInterval(pollInterval);
    pollInterval = null;
  }
}
