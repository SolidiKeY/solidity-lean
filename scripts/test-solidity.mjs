#!/usr/bin/env node
/** Solidity-file testing API. No npm dependencies; proofs are checked by Lean. */
import { existsSync, mkdtempSync, readdirSync, readFileSync, writeFileSync, rmSync, statSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const ignored = new Set([".git", ".lake", "node_modules"]);

/** Stable, deduplicated discovery, including nested suite directories. */
export function solidityFiles(paths) {
  const files = new Set();
  function visit(path) {
    const info = statSync(path);
    if (info.isDirectory()) {
      for (const entry of readdirSync(path, { withFileTypes: true })) {
        if (!ignored.has(entry.name) && !entry.isSymbolicLink()) visit(join(path, entry.name));
      }
    } else if (path.endsWith(".sol")) files.add(path);
  }
  for (const path of paths) visit(resolve(path));
  return [...files].sort();
}

function run(command, args, timeoutMs) {
  const p = spawnSync(command, args, {
    cwd: ROOT, encoding: "utf8", timeout: timeoutMs, maxBuffer: 32 * 1024 * 1024,
  });
  if (p.error || p.status !== 0) {
    throw new Error([p.error?.message, p.stdout, p.stderr].filter(Boolean).join("\n").trim()
      || `${command} exited ${p.status}`);
  }
  return p.stdout;
}

function leanString(s) { return JSON.stringify(s); }
function leanName(s) {
  if (!/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(s)) throw new Error(`unsupported contract name: ${s}`);
  return `SolTests.«${s}»`;
}

/**
 * Compile each source once, discover all its contracts, and test each selected
 * function. Returns { results, errors }; pending is never a counterexample.
 * options: contract, function, list, timeoutMs, solkey, soljson, build.
 * The timeout bounds each compiler/Lean subprocess, including a whole contract.
 */
export function runSolidityTests(paths, options = {}) {
  const files = solidityFiles(paths);
  if (!files.length) throw new Error("no Solidity files selected");
  const timeoutMs = options.timeoutMs ?? 120000;
  if (!Number.isSafeInteger(timeoutMs) || timeoutMs <= 0) throw new Error("timeout must be positive milliseconds");
  if (options.build !== false) run("lake", ["build", "Solidity.Frontend.Testing"], timeoutMs);
  const results = [], errors = [];
  for (const source of files) {
    const scratch = mkdtempSync(join(tmpdir(), "solidity-test-"));
    try {
      const fixture = join(scratch, "source.ast.json");
      const args = ["scripts/solc-ast.mjs", "--source", source, "--out", fixture, "--no-wrapper"];
      for (const key of ["solkey", "soljson"]) if (options[key]) args.push(`--${key}`, resolve(options[key]));
      run(process.execPath, args, timeoutMs);
      const data = readFileSync(fixture);
      let hash = 0xcbf29ce484222325n;
      for (const byte of data) hash = BigInt.asUintN(64, (hash ^ BigInt(byte)) * 0x100000001b3n);
      const contracts = JSON.parse(data).ast.nodes.filter(n => n.nodeType === "ContractDefinition")
        .map(n => n.name).filter(n => !options.contract || n === options.contract).sort();
      if (!contracts.length) throw new Error("no contracts selected");
      for (const contract of contracts) {
        const output = join(scratch, `${contract}.results.json`);
        try {
          const name = leanName(contract);
          const wrapper = join(scratch, "Test.lean");
          writeFileSync(wrapper, `import Solidity.Frontend.Testing
solc_import "source.ast.json" hash 0x${hash.toString(16)} as ${name} testing
solc_scoped_problems ${name} decl
#solkey_test ${name}${options.function ? ` only ${leanString(options.function)}` : ""}${options.list ? " listing" : ""} to ${leanString(output)}
`);
          const diagnostics = run("lake", ["env", "lean", "--tstack=131072", wrapper], timeoutMs);
          // Implicit-constructor gaps are currently warnings, not ImportRows.
          if (diagnostics.includes("warning: solc_import:")) errors.push({ source, contract, reason: diagnostics.trim() });
        } catch (e) { errors.push({ source, contract, reason: e.message }); }
        if (existsSync(output)) {
          try {
            for (const row of JSON.parse(readFileSync(output, "utf8"))) results.push({ source, contract, ...row });
          } catch (e) { errors.push({ source, contract, reason: `invalid result checkpoint: ${e.message}` }); }
        }
      }
    } catch (e) { errors.push({ source, reason: e.message }); }
    finally { rmSync(scratch, { recursive: true, force: true }); }
  }
  return { results, errors };
}

/** Strict success: no pending/unsupported/excluded claims and at least one obligation. */
export function testsPassed(report, listing = false) {
  const active = listing ? "ready" : "proved";
  return report.errors.length === 0 && report.results.some(r => r.status === active)
    && report.results.every(r => [active, "skip", "skipped", "internal"].includes(r.status));
}

function main(args) {
  const options = {}, paths = [];
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg === "--help") {
      console.log("usage: node scripts/test-solidity.mjs [--json] [--list] [--contract NAME] [--function NAME] [--timeout-ms N] [--solkey DIR] [--soljson DIR] [--no-build] FILE_OR_DIR ...");
      return 0;
    } else if (arg === "--json") options.json = true;
    else if (arg === "--list") options.list = true;
    else if (arg === "--no-build") options.build = false;
    else if (["--contract", "--function", "--timeout-ms", "--solkey", "--soljson"].includes(arg)) {
      if (!args[i + 1] || args[i + 1].startsWith("--")) throw new Error(`${arg} needs a value`);
      const key = arg === "--timeout-ms" ? "timeoutMs" : arg.slice(2);
      options[key] = arg === "--timeout-ms" ? Number(args[++i]) : args[++i];
    } else if (arg.startsWith("--")) throw new Error(`unknown option: ${arg}`);
    else paths.push(arg);
  }
  const report = runSolidityTests(paths, options);
  if (options.json) console.log(JSON.stringify(report, null, 2));
  else {
    for (const r of report.results) console.log(`${r.source}:${r.contract}.${r.function}: ${r.status}${r.reason ? ` (${r.reason})` : ""}`);
    for (const e of report.errors) console.error(`${e.source}${e.contract ? `:${e.contract}` : ""}: error: ${e.reason}`);
  }
  return testsPassed(report, options.list) ? 0 : 1;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try { process.exitCode = main(process.argv.slice(2)); }
  catch (e) { console.error(`test-solidity: ${e.message}`); process.exitCode = 2; }
}
