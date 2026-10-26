#!/usr/bin/env node
/** Solidity-file testing API. No npm dependencies; proofs are checked by Lean. */
import { existsSync, mkdtempSync, readdirSync, readFileSync, writeFileSync, rmSync, statSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";
import { sourceHash, sourceLocations, sourceWitness } from './source-locations.mjs';

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

/** Run one bounded tool job; a timed-out Lake job must not leave Lean running. */
export function runTool(command, args, timeoutMs) {
  const group = process.platform !== 'win32';
  const p = spawnSync(command, args, {
    cwd: ROOT, encoding: "utf8", timeout: timeoutMs, maxBuffer: 32 * 1024 * 1024,
    detached: group, killSignal: 'SIGKILL',
  });
  if (p.error || p.status !== 0) {
    if (group && p.pid > 0) {
      try { process.kill(-p.pid, 'SIGKILL'); }
      catch (e) { if (e.code !== 'ESRCH') throw e; }
    }
    const tool = {command, exitCode:p.status, signal:p.signal,
      errorCode:p.error?.code ?? null, timedOut:p.error?.code === 'ETIMEDOUT', timeoutMs};
    const outcome = [p.error?.message,
      p.signal ? `${command} terminated by ${p.signal}` : null,
      p.status !== null ? `${command} exited ${p.status}` : null].filter(Boolean).join('; ');
    const failure = new Error([outcome, p.stdout, p.stderr].filter(Boolean).join("\n").trim());
    failure.tool = tool;
    throw failure;
  }
  return p.stdout;
}

function leanString(s) { return JSON.stringify(s); }
function leanName(s) {
  if (!/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(s)) throw new Error(`unsupported contract name: ${s}`);
  return `SolTests.«${s}»`;
}
function renameClause(renaming = {}) {
  const entries = Object.entries(renaming).map(([from,to]) => {
    leanName(from); leanName(to); // Validate both names before constructing syntax.
    return `«${from}» => «${to}»`;
  });
  return entries.length ? ` renaming ${entries.join(', ')}` : '';
}

/**
 * Compile each source once, discover all its contracts, and test each selected
 * function. Returns { results, errors }; pending is never a counterexample.
 * options: contract, function, list, timeoutMs, solkey, soljson, build, selfAddress,
 * auditPreconditions, counterexamples. Entry audits are independent of the postcondition proof.
 * The timeout bounds each compiler/Lean subprocess, including a whole contract.
 */
export function runSolidityTests(paths, options = {}) {
  const files = solidityFiles(paths);
  if (!files.length) throw new Error("no Solidity files selected");
  if (options.list && options.auditPreconditions)
    throw new Error('precondition auditing requires verification; omit --list');
  if (options.list && options.counterexamples)
    throw new Error('counterexample search requires verification; omit --list');
  const timeoutMs = options.timeoutMs ?? 300000;
  if (!Number.isSafeInteger(timeoutMs) || timeoutMs <= 0) throw new Error("timeout must be positive milliseconds");
  const batchSize = options.batchSize ?? 32;
  if (!Number.isSafeInteger(batchSize) || batchSize <= 0) throw new Error("batch size must be positive");
  // `--self-address A`: every obligation assumes `address(this) == A` (`Problem.selfPre`)
  let selfClause = '';
  if (options.selfAddress !== undefined) {
    if (!/^(0x[0-9a-fA-F]+|[0-9]+)$/.test(String(options.selfAddress))) throw new Error("self address must be a number");
    selfClause = ` self ${BigInt(options.selfAddress).toString()}`;
  }
  if (options.build !== false) runTool("lake", ["build", "Solidity.Frontend.Testing"], timeoutMs);
  const results = [], errors = [];
  for (const source of files) {
    const scratch = mkdtempSync(join(tmpdir(), "solidity-test-"));
    let stage = "compile";
    try {
      const fixture = join(scratch, "source.ast.json");
      const args = ["scripts/solc-ast.mjs", "--source", source, "--out", fixture, "--no-wrapper"];
      for (const key of ["solkey", "soljson"]) if (options[key]) args.push(`--${key}`, resolve(options[key]));
      runTool(process.execPath, args, timeoutMs);
      stage = "discovery";
      const data = readFileSync(fixture);
      const parsed = JSON.parse(data);
      const sourceBytes = readFileSync(source);
      const compiledHash = parsed.header?.sourceSha256;
      if (compiledHash !== sourceHash(sourceBytes))
        throw new Error('source changed during compilation; retry verification');
      const location = sourceLocations(parsed.ast, sourceBytes);
      let hash = 0xcbf29ce484222325n;
      for (const byte of data) hash = BigInt.asUintN(64, (hash ^ BigInt(byte)) * 0x100000001b3n);
      const contracts = JSON.parse(data).ast.nodes.filter(n => n.nodeType === "ContractDefinition")
        .map(n => n.name).filter(n => !options.contract || n === options.contract).sort();
      if (!contracts.length) throw new Error("no contracts selected");
      for (const contract of contracts) {
        function invoke(first, count, listing) {
          const output = join(scratch, `${contract}.${first ?? 'all'}.${listing ? 'list' : 'proof'}.json`);
          const found = [];
          try {
          const name = leanName(contract);
          const wrapper = join(scratch, "Test.lean");
          writeFileSync(wrapper, `import Solidity.Frontend.Testing
solc_import "source.ast.json" hash 0x${hash.toString(16)} as ${name}${renameClause(options.renaming)} testing
solc_scoped_problems ${name} decl${selfClause}
#solkey_test ${name}${options.function ? ` only ${leanString(options.function)}` : ""}${first === undefined ? '' : ` from ${first} count ${count}`}${listing ? " listing" : ""}${options.auditPreconditions && !listing ? " audit_preconditions" : ""}${options.counterexamples && !listing ? " counterexamples" : ""} to ${leanString(output)}
`);
          // `lake lean` supplies the artifact-cache import map. `lake env lean`
          // only sees local oleans, which a freshly cached worktree need not have.
          // The API's build step above owns rebuilding; keep this check read-only.
          const diagnostics = runTool("lake", ["--quiet", "--no-build", "lean", wrapper,
            "--", "--tstack=131072"], timeoutMs);
          // Implicit-constructor gaps are currently warnings, not ImportRows.
          if (diagnostics.includes("warning: solc_import:")) errors.push({ source, contract, reason: diagnostics.trim() });
          } catch (e) { errors.push({ source, contract, stage: "lean", reason: e.message,
            ...(e.tool ? {tool:e.tool} : {}) }); }
        if (existsSync(output)) {
          try {
            for (const row of JSON.parse(readFileSync(output, "utf8"))) found.push({
              ...row, source, contract, sourceHash: compiledHash,
              ...(location(contract, row) ? { range: location(contract, row) } : {}),
              ...(row.counterexample ? {counterexample:sourceWitness(parsed.ast,contract,row)} : {}),
            });
          } catch (e) { errors.push({ source, contract, reason: `invalid result checkpoint: ${e.message}` }); }
        }
          return found;
        }
        const node = JSON.parse(data).ast.nodes.find(n => n.nodeType === 'ContractDefinition' && n.name === contract);
        const large = node.nodes.filter(n => n.nodeType === 'FunctionDefinition').length > batchSize;
        if (!options.list && !options.function && large) {
          const rows = invoke(undefined, undefined, true);
          for (let first=0; first<rows.length; first+=batchSize) {
            const part = invoke(first,batchSize,false);
            // A failed batch with no checkpoint must retain its discovered functions.
            results.push(...(part.length ? part : rows.slice(first,first+batchSize).map(r => ({
              ...r, status:'notRun', reason:'batch failed before checkpoint',
              ...(options.auditPreconditions ? {preconditions:'notRun',preconditionReason:'batch failed before checkpoint'} : {}),
            }))));
            options.onProgress?.({results,errors});
          }
        } else {
          results.push(...invoke(undefined, undefined, options.list));
          options.onProgress?.({results,errors});
        }
      }
    } catch (e) { errors.push({ source, stage, reason: e.message,
      ...(e.tool ? {tool:e.tool} : {}) }); }
    finally { rmSync(scratch, { recursive: true, force: true }); }
  }
  return { results, errors };
}

/** Strict success: no pending/unsupported/excluded claims and at least one obligation. */
export function testsPassed(report, listing = false) {
  const active = listing ? "ready" : "proved";
  return report.errors.length === 0 && report.results.some(r => r.status === active)
    && report.results.every(r => [active, "skip", "skipped", "internal"].includes(r.status)
      && (r.preconditions === undefined || ['possible', 'notApplicable'].includes(r.preconditions)));
}

function main(args) {
  const options = {}, paths = [];
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg === "--help") {
      writeFileSync(1, "usage: node scripts/test-solidity.mjs [--json] [--list] [--audit-preconditions] [--counterexamples] [--contract NAME] [--function NAME] [--timeout-ms N] [--solkey DIR] [--soljson DIR] [--self-address A] [--no-build] FILE_OR_DIR ...\n");
      return 0;
    } else if (arg === "--json") options.json = true;
    else if (arg === "--list") options.list = true;
    else if (arg === "--audit-preconditions") options.auditPreconditions = true;
    else if (arg === "--counterexamples") options.counterexamples = true;
    else if (arg === "--no-build") options.build = false;
    else if (["--contract", "--function", "--timeout-ms", "--solkey", "--soljson", "--self-address"].includes(arg)) {
      if (!args[i + 1] || args[i + 1].startsWith("--")) throw new Error(`${arg} needs a value`);
      const key = arg === "--timeout-ms" ? "timeoutMs" : arg === "--self-address" ? "selfAddress" : arg.slice(2);
      options[key] = arg === "--timeout-ms" ? Number(args[++i]) : args[++i];
    } else if (arg.startsWith("--")) throw new Error(`unknown option: ${arg}`);
    else paths.push(arg);
  }
  const report = runSolidityTests(paths, options);
  // The CLI is also an editor subprocess protocol: finish writing the report
  // before exiting, including when stdout is a pipe with asynchronous writes.
  if (options.json) writeFileSync(1, JSON.stringify(report, null, 2) + '\n');
  else {
    for (const r of report.results) {
      writeFileSync(1, `${r.source}:${r.contract}.${r.function}: ${r.status}${r.reason ? ` (${r.reason})` : ""}${r.preconditions ? `; preconditions: ${r.preconditions}` : ''}\n`);
      if (r.counterexample) {
        writeFileSync(1, '  Certified model prestate (constructor reachability is not established):\n');
        for (const line of r.counterexample.lines) writeFileSync(1, `    ${line}\n`);
      }
    }
    for (const e of report.errors) writeFileSync(2, `${e.source}${e.contract ? `:${e.contract}` : ""}: error: ${e.reason}\n`);
  }
  return testsPassed(report, options.list) ? 0 : 1;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try { process.exitCode = main(process.argv.slice(2)); }
  catch (e) { writeFileSync(2, `test-solidity: ${e.message}\n`); process.exitCode = 2; }
}
