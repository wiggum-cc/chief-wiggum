import { readdir, readFile, stat } from "fs/promises";
import { join } from "path";
import { execSync } from "child_process";

export interface Worker {
  id: string;
  taskId: string;
  timestamp: number;
  pid: number | null;
  status: "running" | "stopped" | "completed" | "failed";
  prdPath: string;
  logPath: string;
  workspacePath: string;
  prUrl: string | null;
}

export interface OrchestratorStatus {
  running: boolean;
  pid: number | null;
}

function isProcessRunning(pid: number): boolean {
  try {
    process.kill(pid, 0);
    return true;
  } catch {
    return false;
  }
}

function isWorkerProcess(pid: number): boolean {
  try {
    const result = execSync(`ps -p ${pid} -o args=`, { encoding: "utf-8" });
    return result.includes("lib/worker.sh");
  } catch {
    return false;
  }
}

function isOrchestratorProcess(pid: number): boolean {
  try {
    const result = execSync(`ps -p ${pid} -o args=`, { encoding: "utf-8" });
    return result.includes("wiggum-run");
  } catch {
    return false;
  }
}

async function getPrdStatus(
  prdPath: string
): Promise<"complete" | "failed" | "incomplete"> {
  try {
    const content = await readFile(prdPath, "utf-8");
    if (content.includes("- [*]")) return "failed";
    if (content.includes("- [ ]")) return "incomplete";
    return "complete";
  } catch {
    return "incomplete";
  }
}

export async function scanWorkers(ralphDir: string): Promise<Worker[]> {
  const workersDir = join(ralphDir, "workers");
  const workers: Worker[] = [];

  try {
    const entries = await readdir(workersDir);

    for (const entry of entries) {
      if (!entry.startsWith("worker-")) continue;

      const workerDir = join(workersDir, entry);
      const stats = await stat(workerDir);
      if (!stats.isDirectory()) continue;

      // Parse worker ID: worker-TASK-XXX-TIMESTAMP
      const match = entry.match(/^worker-([A-Za-z]{2,8}-\d+)-(\d+)$/);
      if (!match) continue;

      const [, taskId, timestampStr] = match;
      const timestamp = parseInt(timestampStr, 10);

      const pidPath = join(workerDir, "worker.pid");
      const prdPath = join(workerDir, "prd.md");
      const logPath = join(workerDir, "worker.log");
      const workspacePath = join(workerDir, "workspace");
      const prUrlPath = join(workerDir, "pr_url.txt");

      let pid: number | null = null;
      let status: Worker["status"] = "stopped";

      // Check PID file
      try {
        const pidContent = await readFile(pidPath, "utf-8");
        const parsedPid = parseInt(pidContent.trim(), 10);
        if (!isNaN(parsedPid)) {
          pid = parsedPid;
          if (isProcessRunning(parsedPid) && isWorkerProcess(parsedPid)) {
            status = "running";
          }
        }
      } catch {
        // No PID file
      }

      // If not running, check PRD status
      if (status !== "running") {
        const prdStatus = await getPrdStatus(prdPath);
        if (prdStatus === "complete") {
          status = "completed";
        } else if (prdStatus === "failed") {
          status = "failed";
        }
      }

      // Check for PR URL
      let prUrl: string | null = null;
      try {
        prUrl = (await readFile(prUrlPath, "utf-8")).trim();
      } catch {
        // No PR URL file
      }

      workers.push({
        id: entry,
        taskId,
        timestamp,
        pid,
        status,
        prdPath,
        logPath,
        workspacePath,
        prUrl,
      });
    }
  } catch {
    // Workers directory doesn't exist
  }

  // Sort by timestamp descending (newest first)
  workers.sort((a, b) => b.timestamp - a.timestamp);

  return workers;
}

export async function getOrchestratorStatus(
  ralphDir: string
): Promise<OrchestratorStatus> {
  const pidPath = join(ralphDir, ".orchestrator.pid");

  try {
    const pidContent = await readFile(pidPath, "utf-8");
    const pid = parseInt(pidContent.trim(), 10);

    if (!isNaN(pid) && isProcessRunning(pid) && isOrchestratorProcess(pid)) {
      return { running: true, pid };
    }
  } catch {
    // No PID file
  }

  return { running: false, pid: null };
}
