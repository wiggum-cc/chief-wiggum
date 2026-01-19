import { writable, get } from "svelte/store";
import type { LogLine } from "../api.js";
import { fetchLogs, subscribeToLogs } from "../api.js";

const MAX_LOG_LINES = 1000;

export const logsStore = writable<LogLine[]>([]);
export const logsLoading = writable(false);
export const logsError = writable<string | null>(null);
export const logsConnected = writable(false);

let eventSource: EventSource | null = null;

export async function loadInitialLogs(): Promise<void> {
  logsLoading.set(true);
  logsError.set(null);

  try {
    const data = await fetchLogs("combined", 500);
    logsStore.set(data.lines);
  } catch (err) {
    logsError.set(err instanceof Error ? err.message : "Unknown error");
  } finally {
    logsLoading.set(false);
  }
}

export function startLogStreaming(): void {
  if (eventSource) return;

  loadInitialLogs();

  eventSource = subscribeToLogs(
    (line) => {
      logsConnected.set(true);
      logsStore.update((lines) => {
        const newLines = [...lines, line];
        if (newLines.length > MAX_LOG_LINES) {
          return newLines.slice(-MAX_LOG_LINES);
        }
        return newLines;
      });
    },
    () => {
      logsConnected.set(false);
      // Reconnect after a delay
      stopLogStreaming();
      setTimeout(startLogStreaming, 5000);
    }
  );

  eventSource.addEventListener("connected", () => {
    logsConnected.set(true);
  });
}

export function stopLogStreaming(): void {
  if (eventSource) {
    eventSource.close();
    eventSource = null;
    logsConnected.set(false);
  }
}

export function clearLogs(): void {
  logsStore.set([]);
}
