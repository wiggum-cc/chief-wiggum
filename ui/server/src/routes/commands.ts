import { Router } from "express";
import {
  startWorkers,
  stopWorkers,
  getStatus,
} from "../services/wiggum-executor.js";

export const commandsRouter = Router();

commandsRouter.post("/run", async (req, res) => {
  try {
    const { maxWorkers } = req.body || {};
    const result = await startWorkers(req.projectDir, { maxWorkers });

    res.json({
      success: result.success,
      message: result.stdout || result.stderr,
    });
  } catch (error) {
    res.status(500).json({
      error: "Failed to start workers",
      message: error instanceof Error ? error.message : "Unknown error",
    });
  }
});

commandsRouter.post("/stop", async (req, res) => {
  try {
    const { orchestrator, pids } = req.body || {};
    const result = await stopWorkers(req.projectDir, { orchestrator, pids });

    res.json({
      success: result.success,
      message: result.stdout || result.stderr,
    });
  } catch (error) {
    res.status(500).json({
      error: "Failed to stop workers",
      message: error instanceof Error ? error.message : "Unknown error",
    });
  }
});

commandsRouter.get("/status", async (req, res) => {
  try {
    const result = await getStatus(req.projectDir);

    res.json({
      success: result.success,
      output: result.stdout,
      error: result.stderr,
    });
  } catch (error) {
    res.status(500).json({
      error: "Failed to get status",
      message: error instanceof Error ? error.message : "Unknown error",
    });
  }
});
