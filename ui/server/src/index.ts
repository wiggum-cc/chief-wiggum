import express from "express";
import cors from "cors";
import { kanbanRouter } from "./routes/kanban.js";
import { workersRouter } from "./routes/workers.js";
import { logsRouter } from "./routes/logs.js";
import { commandsRouter } from "./routes/commands.js";
import { conversationRouter } from "./routes/conversation.js";

const app = express();
const PORT = process.env.PORT || 3001;

// Get project directory from environment or use parent of ui/
const PROJECT_DIR =
  process.env.WIGGUM_PROJECT_DIR || new URL("../../..", import.meta.url).pathname;

app.use(cors());
app.use(express.json());

// Make project directory available to all routes
app.use((req, res, next) => {
  req.projectDir = PROJECT_DIR;
  req.ralphDir = `${PROJECT_DIR}/.ralph`;
  next();
});

// Routes
app.use("/api/kanban", kanbanRouter);
app.use("/api/workers", workersRouter);
app.use("/api/logs", logsRouter);
app.use("/api", commandsRouter);
app.use("/api/conversation", conversationRouter);

// Health check
app.get("/api/health", (req, res) => {
  res.json({ status: "ok", projectDir: req.projectDir });
});

app.listen(PORT, () => {
  console.log(`Server running on http://localhost:${PORT}`);
  console.log(`Project directory: ${PROJECT_DIR}`);
});

// Extend Express Request type
declare global {
  namespace Express {
    interface Request {
      projectDir: string;
      ralphDir: string;
    }
  }
}
