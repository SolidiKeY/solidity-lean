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
  ["g07 script tests", "node", ["--test", "scripts/check-noncircular.test.mjs", "scripts/check-axiom-pins.test.mjs"]],
]) {
  const r = run(cmd, args);
  const fails = r.out.split("\n").filter((l) => /^(ERROR|NOTE|LAYER|WHITELIST|LATER|EVM-END|CONTROL|DATATYPE|not ok)\b|forbidden|drift/.test(l));
  report(name, r.code === 0, name === "g07 script tests" ? (r.out.match(/# pass \d+/)?.[0] ?? last(r.out)) : last(r.out), fails.slice(0, 20));
}

{
  const r = run("bash", ["scripts/check-doc-paths.sh"]);
  const missing = r.out.split("\n").filter((l) => l.startsWith("missing:"));
  const known = new Set(baseline.docPaths.missing);
  const added = missing.filter((l) => !known.has(l));
  report("check-doc-paths", added.length === 0,
    `${missing.length} missing (${known.size} baselined, ${added.length} new)`, added);
}

{
  const r = run("python3", ["-I", "scripts/roadmap-g03-ledger.py", "--check"]);
  const errors = r.out.split("\n").filter((l) => l && !l.startsWith("roadmap-g03:"));
  const known = new Set(baseline.g03Ledger.errors);
  const added = errors.filter((l) => !known.has(l));
  report("roadmap-g03-ledger --check", added.length === 0,
    `${errors.length} errors (${known.size} baselined, ${added.length} new)`, added);
}

const i = process.argv.indexOf("--log");
if (i > 0) {
  const log = readFileSync(process.argv[i + 1], "utf8").split("\n");
  const oom = baseline.build.knownOom;
  const errs = log.filter((l) => /\berror\b/i.test(l) && !oom.some((m) => l.includes(m)));
  report("run-lean errors", errs.length === 0, `${errs.length} error lines outside ${oom.join(", ")}`, errs.slice(0, 20));
  const mm = log.map((l) => l.match(/(\d+) mismatch\(es\)/)).filter(Boolean).map((m) => +m[1]);
  const n = mm.at(-1);
  report("check-solkey mismatches", n === undefined || n <= baseline.build.solkeyMismatches,
    n === undefined ? "no count in log" : `${n} (baseline ${baseline.build.solkeyMismatches})`);
  const oomHits = log.filter((l) => oom.some((m) => l.includes(m)) && /137|error/i.test(l));
  console.log(`old  known out-of-memory lines: ${oomHits.length}`);
}

console.log(`g07: ${fresh} new failure(s)`);
process.exit(fresh ? 1 : 0);
