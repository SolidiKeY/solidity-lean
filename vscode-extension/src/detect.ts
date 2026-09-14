/**
 * Package-directory detection and the lean invocation, shared by the
 * extension and the CLI. Node-only (fs, path, os, child_process); no vscode.
 */

import * as cp from "child_process";
import * as fs from "fs";
import * as os from "os";
import * as path from "path";

/** A package dir has a lakefile.toml and Solidity.lean side by side. */
export function isPackageDir(dir: string): boolean {
  try {
    return (
      fs.existsSync(path.join(dir, "lakefile.toml")) &&
      fs.existsSync(path.join(dir, "Solidity.lean"))
    );
  } catch {
    return false;
  }
}

/** Walk up from startDir looking for a package dir. */
export function findPackageDirUp(startDir: string): string | undefined {
  let dir = path.resolve(startDir);
  for (;;) {
    if (isPackageDir(dir)) {
      return dir;
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      return undefined;
    }
    dir = parent;
  }
}

const SKIP_DIRS = new Set(["node_modules", ".git", ".lake", ".gen", "out", "build", ".vscode"]);

/** Bounded breadth-first scan of the given roots for a package dir. */
export function scanForPackageDir(roots: string[], maxDepth = 3): string | undefined {
  const queue: Array<{ dir: string; depth: number }> = roots.map((r) => ({ dir: r, depth: 0 }));
  while (queue.length > 0) {
    const { dir, depth } = queue.shift()!;
    if (isPackageDir(dir)) {
      return dir;
    }
    if (depth >= maxDepth) {
      continue;
    }
    let entries: fs.Dirent[];
    try {
      entries = fs.readdirSync(dir, { withFileTypes: true });
    } catch {
      continue;
    }
    for (const e of entries) {
      if (e.isDirectory() && !SKIP_DIRS.has(e.name) && !e.name.startsWith(".")) {
        queue.push({ dir: path.join(dir, e.name), depth: depth + 1 });
      }
    }
  }
  return undefined;
}

/** PATH with ~/.elan/bin prefixed. */
export function elanPath(): string {
  const elanBin = path.join(os.homedir(), ".elan", "bin");
  return `${elanBin}${path.delimiter}${process.env.PATH ?? ""}`;
}

/** Write the generated Lean file into <packageDir>/.gen/ and return its path. */
export function writeGeneratedFile(packageDir: string, fileName: string, text: string): string {
  const genDir = path.join(packageDir, ".gen");
  fs.mkdirSync(genDir, { recursive: true });
  const genPath = path.join(genDir, fileName);
  fs.writeFileSync(genPath, text, "utf8");
  return genPath;
}

export interface LeanRunResult {
  stdout: string;
  stderr: string;
  exitCode: number | null;
  /** Set when the process could not be spawned at all. */
  spawnError?: string;
}

/**
 * Run `lake build <target>` with cwd = packageDir.
 *
 * The SolSpec flow needs it: generated obligation files import
 * `Solidity.Spec.Tactic`, which is deliberately not
 * part of the default `lake build` (see the lakefile), so `lake env lean`
 * would not find its olean. Cached after the first run.
 */
export function runLakeBuild(
  lakeCommand: string,
  packageDir: string,
  target: string,
  timeoutMs = 1_800_000,
): Promise<LeanRunResult> {
  return spawnLake(lakeCommand, packageDir, ["build", target], timeoutMs);
}

/** Run `lake env lean --json <genPath>` with cwd = packageDir. */
export function runLean(
  lakeCommand: string,
  packageDir: string,
  genPath: string,
  timeoutMs = 600_000,
): Promise<LeanRunResult> {
  return spawnLake(lakeCommand, packageDir, ["env", "lean", "--json", genPath], timeoutMs);
}

function spawnLake(
  lakeCommand: string,
  packageDir: string,
  args: string[],
  timeoutMs: number,
): Promise<LeanRunResult> {
  return new Promise((resolve) => {
    const child = cp.spawn(lakeCommand, args, {
      cwd: packageDir,
      env: { ...process.env, PATH: elanPath() },
    });
    let stdout = "";
    let stderr = "";
    let done = false;
    const timer = setTimeout(() => {
      if (!done) {
        child.kill();
        done = true;
        resolve({
          stdout,
          stderr,
          exitCode: null,
          spawnError: `${lakeCommand} ${args.join(" ")} timed out after ${timeoutMs}ms`,
        });
      }
    }, timeoutMs);
    child.stdout.on("data", (d) => (stdout += d.toString()));
    child.stderr.on("data", (d) => (stderr += d.toString()));
    child.on("error", (err) => {
      if (!done) {
        done = true;
        clearTimeout(timer);
        resolve({ stdout, stderr, exitCode: null, spawnError: err.message });
      }
    });
    child.on("close", (code) => {
      if (!done) {
        done = true;
        clearTimeout(timer);
        resolve({ stdout, stderr, exitCode: code });
      }
    });
  });
}
