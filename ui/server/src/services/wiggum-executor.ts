import { spawn, execSync } from "child_process";
import { join } from "path";

export interface CommandResult {
  success: boolean;
  stdout: string;
  stderr: string;
  exitCode: number | null;
}

// Allowed wiggum subcommands for safety
const ALLOWED_COMMANDS = ["run", "stop", "status", "validate", "clean"];

export async function runWiggum(
  projectDir: string,
  args: string[]
): Promise<CommandResult> {
  // Validate command
  if (args.length === 0 || !ALLOWED_COMMANDS.includes(args[0])) {
    return {
      success: false,
      stdout: "",
      stderr: `Invalid command. Allowed: ${ALLOWED_COMMANDS.join(", ")}`,
      exitCode: 1,
    };
  }

  const wiggumPath = join(projectDir, "bin", "wiggum");

  return new Promise((resolve) => {
    const proc = spawn(wiggumPath, args, {
      cwd: projectDir,
      env: { ...process.env, PATH: `${projectDir}/bin:${process.env.PATH}` },
    });

    let stdout = "";
    let stderr = "";

    proc.stdout.on("data", (data) => {
      stdout += data.toString();
    });

    proc.stderr.on("data", (data) => {
      stderr += data.toString();
    });

    proc.on("close", (exitCode) => {
      resolve({
        success: exitCode === 0,
        stdout,
        stderr,
        exitCode,
      });
    });

    proc.on("error", (error) => {
      resolve({
        success: false,
        stdout,
        stderr: error.message,
        exitCode: null,
      });
    });
  });
}

export async function startWorkers(
  projectDir: string,
  options: { maxWorkers?: number } = {}
): Promise<CommandResult> {
  const args = ["run"];
  if (options.maxWorkers) {
    args.push("--max-workers", options.maxWorkers.toString());
  }

  // Run in background - spawn detached process
  const wiggumPath = join(projectDir, "bin", "wiggum");

  return new Promise((resolve) => {
    const proc = spawn(wiggumPath, args, {
      cwd: projectDir,
      env: { ...process.env, PATH: `${projectDir}/bin:${process.env.PATH}` },
      detached: true,
      stdio: "ignore",
    });

    proc.unref();

    // Give it a moment to start
    setTimeout(() => {
      resolve({
        success: true,
        stdout: `Started wiggum run (PID: ${proc.pid})`,
        stderr: "",
        exitCode: 0,
      });
    }, 500);
  });
}

export async function stopWorkers(
  projectDir: string,
  options: { pids?: number[]; orchestrator?: boolean } = {}
): Promise<CommandResult> {
  const args = ["stop"];

  if (options.orchestrator) {
    args.push("--orchestrator");
  } else if (options.pids && options.pids.length > 0) {
    args.push("--workers", options.pids.join(","));
  }

  return runWiggum(projectDir, args);
}

export function stopWorkerByPid(pid: number): boolean {
  try {
    process.kill(pid, "SIGTERM");
    return true;
  } catch {
    return false;
  }
}

export async function getStatus(projectDir: string): Promise<CommandResult> {
  return runWiggum(projectDir, ["status"]);
}
