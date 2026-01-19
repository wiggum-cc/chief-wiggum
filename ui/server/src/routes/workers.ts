import { Router } from "express";
import {
  scanWorkers,
  getOrchestratorStatus,
} from "../services/worker-scanner.js";
import { stopWorkerByPid } from "../services/wiggum-executor.js";

export const workersRouter = Router();

workersRouter.get("/", async (req, res) => {
  try {
    const workers = await scanWorkers(req.ralphDir);
    const orchestrator = await getOrchestratorStatus(req.ralphDir);

    res.json({
      workers,
      orchestrator,
      counts: {
        running: workers.filter((w) => w.status === "running").length,
        stopped: workers.filter((w) => w.status === "stopped").length,
        completed: workers.filter((w) => w.status === "completed").length,
        failed: workers.filter((w) => w.status === "failed").length,
        total: workers.length,
      },
    });
  } catch (error) {
    res.status(500).json({
      error: "Failed to scan workers",
      message: error instanceof Error ? error.message : "Unknown error",
    });
  }
});

workersRouter.get("/:id", async (req, res) => {
  try {
    const workers = await scanWorkers(req.ralphDir);
    const worker = workers.find((w) => w.id === req.params.id);

    if (!worker) {
      return res.status(404).json({ error: "Worker not found" });
    }

    res.json({ worker });
  } catch (error) {
    res.status(500).json({
      error: "Failed to get worker",
      message: error instanceof Error ? error.message : "Unknown error",
    });
  }
});

workersRouter.post("/:id/stop", async (req, res) => {
  try {
    const workers = await scanWorkers(req.ralphDir);
    const worker = workers.find((w) => w.id === req.params.id);

    if (!worker) {
      return res.status(404).json({ error: "Worker not found" });
    }

    if (!worker.pid) {
      return res.status(400).json({ error: "Worker has no PID" });
    }

    if (worker.status !== "running") {
      return res.status(400).json({ error: "Worker is not running" });
    }

    const success = stopWorkerByPid(worker.pid);

    res.json({ success, message: success ? "Worker stopped" : "Failed to stop worker" });
  } catch (error) {
    res.status(500).json({
      error: "Failed to stop worker",
      message: error instanceof Error ? error.message : "Unknown error",
    });
  }
});
