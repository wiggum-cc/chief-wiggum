import { Router } from "express";
import { join } from "path";
import {
  parseIterationLogs,
  groupIntoTurns,
} from "../services/conversation-parser.js";

export const conversationRouter = Router();

conversationRouter.get("/:workerId", async (req, res) => {
  try {
    const workerDir = join(req.ralphDir, "workers", req.params.workerId);
    const { messages, initialPrompt, iterationResults } = await parseIterationLogs(workerDir);
    const turns = groupIntoTurns(messages);

    res.json({
      messages,
      turns,
      initialPrompt,
      iterationResults,
      messageCount: messages.length,
      turnCount: turns.length,
    });
  } catch (error) {
    res.status(500).json({
      error: "Failed to parse conversation",
      message: error instanceof Error ? error.message : "Unknown error",
    });
  }
});
