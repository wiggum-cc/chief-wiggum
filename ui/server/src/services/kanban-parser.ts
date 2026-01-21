import { readFile } from "fs/promises";

export interface Task {
  id: string;
  title: string;
  status: "pending" | "in_progress" | "complete" | "failed";
  description: string;
  priority: "CRITICAL" | "HIGH" | "MEDIUM" | "LOW";
  complexity?: "HIGH" | "MEDIUM" | "LOW";
  dependencies: string[];
  scope: string[];
  outOfScope: string[];
  acceptanceCriteria: string[];
}

type TaskStatus = Task["status"];

const STATUS_MAP: Record<string, TaskStatus> = {
  "[ ]": "pending",
  "[=]": "in_progress",
  "[x]": "complete",
  "[*]": "failed",
};

export async function parseKanban(filePath: string): Promise<Task[]> {
  let content: string;
  try {
    content = await readFile(filePath, "utf-8");
  } catch {
    return [];
  }

  const lines = content.split("\n");
  const tasks: Task[] = [];
  let currentTask: Task | null = null;
  let currentField: "scope" | "outOfScope" | "acceptanceCriteria" | null = null;

  for (const line of lines) {
    // Check for task line: - [ ] **[TASK-ID]** Title
    const taskMatch = line.match(
      /^- \[([ =x*])\] \*\*\[([A-Za-z]{2,8}-\d+)\]\*\*\s*(.*)/
    );

    if (taskMatch) {
      // Save previous task
      if (currentTask) {
        tasks.push(currentTask);
      }

      const [, statusChar, taskId, title] = taskMatch;
      const status = STATUS_MAP[`[${statusChar}]`] || "pending";

      currentTask = {
        id: taskId,
        title: title.trim(),
        status,
        description: "",
        priority: "MEDIUM",
        dependencies: [],
        scope: [],
        outOfScope: [],
        acceptanceCriteria: [],
      };
      currentField = null;
      continue;
    }

    if (!currentTask) continue;

    // Check for field lines (2-space indent)
    if (line.startsWith("  - ")) {
      const fieldLine = line.slice(4);

      if (fieldLine.startsWith("Description:")) {
        currentTask.description = fieldLine.slice(12).trim();
        currentField = null;
      } else if (fieldLine.startsWith("Priority:")) {
        const priority = fieldLine.slice(9).trim().toUpperCase();
        if (["CRITICAL", "HIGH", "MEDIUM", "LOW"].includes(priority)) {
          currentTask.priority = priority as Task["priority"];
        }
        currentField = null;
      } else if (fieldLine.startsWith("Complexity:")) {
        const complexity = fieldLine.slice(11).trim().toUpperCase();
        if (["HIGH", "MEDIUM", "LOW"].includes(complexity)) {
          currentTask.complexity = complexity as Task["complexity"];
        }
        currentField = null;
      } else if (fieldLine.startsWith("Dependencies:")) {
        const deps = fieldLine.slice(13).trim();
        if (deps && deps.toLowerCase() !== "none") {
          currentTask.dependencies = deps.split(",").map((d) => d.trim());
        }
        currentField = null;
      } else if (fieldLine.startsWith("Scope:") || fieldLine === "Scope") {
        currentField = "scope";
      } else if (
        fieldLine.startsWith("Out of Scope:") ||
        fieldLine === "Out of Scope"
      ) {
        currentField = "outOfScope";
      } else if (
        fieldLine.startsWith("Acceptance Criteria:") ||
        fieldLine === "Acceptance Criteria"
      ) {
        currentField = "acceptanceCriteria";
      }
      continue;
    }

    // Check for sub-items (4-space indent)
    if (line.startsWith("    - ") && currentField) {
      const item = line.slice(6).trim();
      currentTask[currentField].push(item);
    }
  }

  // Don't forget the last task
  if (currentTask) {
    tasks.push(currentTask);
  }

  return tasks;
}

export function groupTasksByStatus(tasks: Task[]): Record<TaskStatus, Task[]> {
  return {
    pending: tasks.filter((t) => t.status === "pending"),
    in_progress: tasks.filter((t) => t.status === "in_progress"),
    complete: tasks.filter((t) => t.status === "complete"),
    failed: tasks.filter((t) => t.status === "failed"),
  };
}
