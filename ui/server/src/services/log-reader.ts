import { readFile, stat } from "fs/promises";
import { watch, FSWatcher } from "fs";

export interface LogLine {
  raw: string;
  timestamp: string | null;
  level: string | null;
  message: string;
}

const LOG_LINE_REGEX = /^\[([^\]]+)\]\s+(DEBUG|INFO|WARN|ERROR):\s*(.*)$/;

export function parseLogLine(line: string): LogLine {
  const match = line.match(LOG_LINE_REGEX);
  if (match) {
    return {
      raw: line,
      timestamp: match[1],
      level: match[2],
      message: match[3],
    };
  }
  return {
    raw: line,
    timestamp: null,
    level: null,
    message: line,
  };
}

export async function readLog(
  logPath: string,
  maxLines = 500
): Promise<LogLine[]> {
  try {
    const content = await readFile(logPath, "utf-8");
    const lines = content.split("\n").filter((line) => line.trim());

    // Return last N lines
    const startIndex = Math.max(0, lines.length - maxLines);
    return lines.slice(startIndex).map(parseLogLine);
  } catch {
    return [];
  }
}

export async function getLogSize(logPath: string): Promise<number> {
  try {
    const stats = await stat(logPath);
    return stats.size;
  } catch {
    return 0;
  }
}

export class LogTailer {
  private watcher: FSWatcher | null = null;
  private lastSize = 0;
  private logPath: string;
  private callback: (lines: LogLine[]) => void;

  constructor(logPath: string, callback: (lines: LogLine[]) => void) {
    this.logPath = logPath;
    this.callback = callback;
  }

  async start(): Promise<void> {
    this.lastSize = await getLogSize(this.logPath);

    this.watcher = watch(this.logPath, async (eventType) => {
      if (eventType === "change") {
        await this.checkForNewContent();
      }
    });
  }

  private async checkForNewContent(): Promise<void> {
    try {
      const currentSize = await getLogSize(this.logPath);

      if (currentSize > this.lastSize) {
        // Read new content
        const content = await readFile(this.logPath, "utf-8");
        const allLines = content.split("\n");

        // Calculate approximate line position based on size difference
        // This is a simplification - for better accuracy, track byte positions
        const newContent = content.slice(this.lastSize);
        const newLines = newContent
          .split("\n")
          .filter((line) => line.trim())
          .map(parseLogLine);

        if (newLines.length > 0) {
          this.callback(newLines);
        }

        this.lastSize = currentSize;
      }
    } catch {
      // File might have been rotated or deleted
    }
  }

  stop(): void {
    if (this.watcher) {
      this.watcher.close();
      this.watcher = null;
    }
  }
}
