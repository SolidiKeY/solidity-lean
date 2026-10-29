#!/usr/bin/env node
// Roadmap G07: the proof/trust regression gate
// (docs/feature-work/roadmap-g07-gates.md). Runs the Lean-free gates and
// compares the ones with existing failures against the recorded baseline
// `scripts/g07-baseline.json`, so that an old failure is reported apart from
// a new one and only a new one fails the gate.
//
//   must pass:   check-trust.sh, check-layers, check-orphans,
//                check-noncircular, check-axiom-pins, the node tests of the
//                G07 scripts
//   baselined:   check-doc-paths.sh (missing references),
//                roadmap-g03-ledger.py --check (error lines)
//   with --log:  a `./run-lean.sh` log: Lean errors outside the baselined
//                out-of-memory modules, and the SolKey mismatch count
//
// Usage: node scripts/check-g07.mjs [--log RUN_LEAN_LOG]
// Exit 0 = no new failure, 1 = a new failure (printed as NEW).
import { readFileSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const baseline = JSON.parse(readFileSync(resolve(root, "scripts/g07-baseline.json"), "utf8"));
const run = (cmd, args) => {
  const r = spawnSync(cmd, args, { cwd: root, encoding: "utf8", maxBuffer: 1 << 28 });
  return { code: r.status, out: (r.stdout ?? "") + (r.stderr ?? "") };
};
const last = (s) => s.trim().split("\n").at(-1);
let fresh = 0;
const report = (name, ok, line, extra = []) => {
  console.log(`${ok ? "ok  " : "NEW "} ${name}: ${line}`);
  for (const e of extra) console.log(`       ${e}`);
  if (!ok) fresh++;
};

for (const [name, cmd, args] of [
  ["check-trust", "bash", ["scripts/check-trust.sh"]],
  ["check-layers", "node", ["scripts/check-layers.mjs"]],
  ["check-orphans", "node", ["scripts/check-orphans.mjs"]],
  ["check-noncircular", "node", ["scripts/check-noncircular.mjs"]],
  ["check-axiom-pins", "node", ["scripts/check-axiom-pins.mjs"]],
  ["check-source-grammar", "node", ["scripts/check-source-grammar.mjs"]],
  ["g07 script tests", "node", ["--test", "scripts/check-noncircular.test.mjs", "scripts/check-axiom-pins.test.mjs"]],
]) {
  const r = run(cmd, args);
  const fails = r.out.split("\n").filter((l) => /^(ERROR|NOTE|LAYER|WHITELIST|LATER|EVM-END|CONTROL|DATATYPE|not ok)\b|forbidden|drift/.test(l));
  report(name, r.code === 0, name === "g07 script tests" ? (r.out.match(/# pass \d+/)?.[0] ?? last(r.out)) : last(r.out), fails.slice(0, 20));
}

// Lines of a baselined gate: backticks dropped, so the baseline file cites
// no path itself; compared as multisets.
const strip = (l) => l.replaceAll("`", "");
const newLines = (lines, known) => {
  const left = new Map();
  for (const k of known) left.set(k, (left.get(k) ?? 0) + 1);
  return lines.filter((l) => {
    const n = left.get(l) ?? 0;
    if (n > 0) { left.set(l, n - 1); return false; }
    return true;
  });
};

{
  const r = run("bash", ["scripts/check-doc-paths.sh"]);
  const summary = r.out.match(/FAIL: (\d+) reference\(s\)|^OK\b.*$/mu);
  const missing = r.out.split("\n").filter((l) => l.startsWith("missing:")).map(strip);
  const added = newLines(missing, baseline.docPaths.missing);
  const sane = (r.code === 0 || r.code === 1) && summary && (summary[1] === undefined || +summary[1] === missing.length);
  report("check-doc-paths", sane && added.length === 0,
    sane ? `${missing.length} missing (${baseline.docPaths.missing.length} baselined, ${added.length} new)` : `no summary line (exit ${r.code})`, added);
}

{
  const r = run("python3", ["-I", "scripts/roadmap-g03-ledger.py", "--check"]);
  const summary = r.out.match(/^roadmap-g03: (\d+) error\(s\)|^roadmap-g03: (ok|OK)/mu);
  const errors = r.out.split("\n").filter((l) => l && !l.startsWith("roadmap-g03:")).map(strip);
  const added = newLines(errors, baseline.g03Ledger.errors);
  const sane = (r.code === 0 || r.code === 1) && summary !== null;
  report("roadmap-g03-ledger --check", sane && added.length === 0,
    sane ? `${errors.length} errors (${baseline.g03Ledger.errors.length} baselined, ${added.length} new)` : `no summary line (exit ${r.code})`, added);
}

{
  // The controls must stay: each named theorem keeps a pin in the inventory.
  const inv = JSON.parse(readFileSync(resolve(root, "scripts/g07-axiom-pins.json"), "utf8"));
  const pinned = new Set(Object.keys(inv).map((k) => k.slice(k.indexOf(":") + 1)));
  const gone = baseline.requiredPins.filter((n) => !pinned.has(n));
  report("required control pins", gone.length === 0, `${baseline.requiredPins.length - gone.length}/${baseline.requiredPins.length} present`, gone);
}

const i = process.argv.indexOf("--log");
if (i > 0) {
  if (!process.argv[i + 1]) throw new Error("--log needs a file");
  const log = readFileSync(process.argv[i + 1], "utf8").split("\n");
  const oom = baseline.build.knownOom;
  const oomLine = (l) => oom.some((m) => l.includes(m)) && /137|Killed|out of memory/iu.test(l);
  const errs = log.filter((l) => /\berror\b/iu.test(l) && !oomLine(l));
  report("run-lean errors", errs.length === 0, `${errs.length} error lines outside the baselined out-of-memory kills`, errs.slice(0, 20));
  const done = log.filter((l) => /Build completed successfully/u.test(l)).length;
  report("run-lean completion", done >= 1, `${done} "Build completed successfully" lines`);
  const mm = log.map((l) => l.match(/(\d+) mismatch\(es\)/u)).filter(Boolean).map((m) => +m[1]);
  const n = mm.at(-1);
  report("check-solkey mismatches", n !== undefined && n <= baseline.build.solkeyMismatches,
    n === undefined ? "no count in log" : `${n} (baseline ${baseline.build.solkeyMismatches}; compared by count only)`);
  console.log(`old  known out-of-memory kills: ${log.filter(oomLine).length}`);
}

console.log(`g07: ${fresh} new failure(s)`);
process.exit(fresh ? 1 : 0);
