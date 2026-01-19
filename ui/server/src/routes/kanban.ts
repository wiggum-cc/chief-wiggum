import { Router } from "express";
import { join } from "path";
import { parseKanban, groupTasksByStatus } from "../services/kanban-parser.js";

export const kanbanRouter = Router();

kanbanRouter.get("/", async (req, res) => {
  try {
    const kanbanPath = join(req.ralphDir, "kanban.md");
    const tasks = await parseKanban(kanbanPath);
    const grouped = groupTasksByStatus(tasks);

    res.json({
      tasks,
      grouped,
      counts: {
        pending: grouped.pending.length,
        in_progress: grouped.in_progress.length,
        complete: grouped.complete.length,
        failed: grouped.failed.length,
        total: tasks.length,
      },
    });
  } catch (error) {
    res.status(500).json({
      error: "Failed to parse kanban",
      message: error instanceof Error ? error.message : "Unknown error",
    });
  }
});
