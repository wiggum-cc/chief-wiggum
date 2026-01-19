import { Router } from "express";
import { join } from "path";
import { readLog, LogTailer, LogLine } from "../services/log-reader.js";

export const logsRouter = Router();

logsRouter.get("/combined", async (req, res) => {
  try {
    const logPath = join(req.ralphDir, "logs", "workers.log");
    const maxLines = parseInt(req.query.lines as string) || 500;
    const lines = await readLog(logPath, maxLines);

    res.json({ lines, path: logPath });
  } catch (error) {
    res.status(500).json({
      error: "Failed to read logs",
      message: error instanceof Error ? error.message : "Unknown error",
    });
  }
});

logsRouter.get("/audit", async (req, res) => {
  try {
    const logPath = join(req.ralphDir, "logs", "audit.log");
    const maxLines = parseInt(req.query.lines as string) || 500;
    const lines = await readLog(logPath, maxLines);

    res.json({ lines, path: logPath });
  } catch (error) {
    res.status(500).json({
      error: "Failed to read audit logs",
      message: error instanceof Error ? error.message : "Unknown error",
    });
  }
});

logsRouter.get("/worker/:id", async (req, res) => {
  try {
    const logPath = join(req.ralphDir, "workers", req.params.id, "worker.log");
    const maxLines = parseInt(req.query.lines as string) || 500;
    const lines = await readLog(logPath, maxLines);

    res.json({ lines, path: logPath });
  } catch (error) {
    res.status(500).json({
      error: "Failed to read worker logs",
      message: error instanceof Error ? error.message : "Unknown error",
    });
  }
});

// SSE endpoint for real-time log streaming
logsRouter.get("/stream", (req, res) => {
  const logPath = join(req.ralphDir, "logs", "workers.log");

  // Set up SSE
  res.setHeader("Content-Type", "text/event-stream");
  res.setHeader("Cache-Control", "no-cache");
  res.setHeader("Connection", "keep-alive");
  res.flushHeaders();

  // Send initial heartbeat
  res.write("event: connected\ndata: {}\n\n");

  // Start tailing
  const tailer = new LogTailer(logPath, (lines: LogLine[]) => {
    for (const line of lines) {
      res.write(`event: log\ndata: ${JSON.stringify(line)}\n\n`);
    }
  });

  tailer.start().catch(() => {
    // Log file might not exist yet
  });

  // Heartbeat to keep connection alive
  const heartbeat = setInterval(() => {
    res.write("event: heartbeat\ndata: {}\n\n");
  }, 30000);

  // Cleanup on disconnect
  req.on("close", () => {
    clearInterval(heartbeat);
    tailer.stop();
  });
});
