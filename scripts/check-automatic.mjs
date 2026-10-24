#!/usr/bin/env node
/**
 * The automation gate: every derived TestSuite obligation closes by the
 * automatic prover, and none is pending.  No Lean is run.
 *
 * A proof is automatic when it is a `sol_auto_theorem` (`Calculus/Closers.lean`),
 * or its body is `sol_prove` (a step budget
 * `(steps := n)` allowed), followed only by the replay `sol_prove?`
 * suggests for the leaves the walk leaves: per leaf, `sol_leaf` and one of
 * `Derive.leafTacs`' closers (`Calculus/Derive.lean`), under `case leafN =>`
 * bare for a single leaf, or under `all_goals` for every leaf alike.  Anything else in the body (a rewrite, an
 * `intro`, an `omega`), and any `set_option` on the theorem, is manual.
 * A refutation (`N.f.refuted : ¬ (⊢ N.f.problem)`) is automatic when it
 * is in `Refuted.lean` and is `sol_refute` alone, which proves it from
 * `¬ ⊨ᶠ N.f.problem` (a certified counterexample).  The counts read here
 * must be the pin's.
 * Pending obligations are read off the `#solkey_obligations` pin in
 * `Solidity/TestSuite/Report.lean`.
 *
 * Usage: node scripts/check-automatic.mjs [--strict] [--build-log <file>] [--budget-s <n>]
 *   --strict     exit 1 on a manual proof or a pending obligation (the
 *                gate); without it only manual proofs fail.  A step budget
 *                is the stage `sol_prove` found by itself (`Seq.prove`'s
 *                stages), written so the replay does not search again:
 *                automatic.
 *   --build-log  the output of `lake build SolkeyTestSuite`: every TestSuite
 *                module it built must have taken at most `--budget-s`
 *                seconds (default 300; the slowest takes about 100 s on a
 *                laptop).  A module the cache replayed is not timed.
 */
import { readdirSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const DIR = join(ROOT, "Solidity/TestSuite");
const strict = process.argv.includes("--strict");
const optionOf = (name, dflt) => {
  const i = process.argv.indexOf(name);
  return i < 0 ? dflt : process.argv[i + 1];
};
const buildLog = optionOf("--build-log", null);
const budget = Number(optionOf("--budget-s", "300"));

/** Lake's duration, `476ms`, `8.8s`, `2m 3s` or `1.5m`, in seconds. */
export function seconds(d) {
  let total = 0;
  for (const [, n, u] of d.matchAll(/([\d.]+)\s*(ms|s|m|h)/g))
    total += Number(n) * { ms: 0.001, s: 1, m: 60, h: 3600 }[u];
  return total;
}

/** The TestSuite modules a build log shows built, with their seconds. */
export function timings(log) {
  return [...log.matchAll(/Built (Solidity\.TestSuite\.\S+) \(([^)]*)\)/g)]
    .map(([, m, d]) => [m, seconds(d)]);
}

const closers = new Set(["sol_decide", "sol_close", "sol_spec_close"]);
const proveLine = /^sol_prove(?: \(steps := (\d+)\))?$/;

/** Classify one proof body (its lines, trimmed, comments dropped). */
export function classify(lines) {
  const [head, ...rest] = lines;
  if (head === "sol_auto" && rest.length === 0) return { kind: "auto", steps: null };
  const m = head?.match(proveLine);
  if (!m) return { kind: "manual", why: `starts with \`${head ?? ""}\`` };
  const leaf = (ls) => ls.length === 2 && ["sol_leaf", "sol_leaf_keep"].includes(ls[0]) &&
    closers.has(ls[1]);
  const every = (ls) => ls.length === 2 && ls[0] === "all_goals sol_leaf" &&
    ls[1].startsWith("all_goals ") && closers.has(ls[1].slice(10));
  if (every(rest)) {
    // the same replay for every leaf at once
  } else if (rest.length > 0 && !rest[0].startsWith("case ")) {
    if (!leaf(rest)) return { kind: "manual", why: `leaf by \`${rest.join("; ")}\`` };
  } else {
    for (let i = 0; i < rest.length; i += 3) {
      if (!/^case leaf\d+ =>$/.test(rest[i]) || !leaf(rest.slice(i + 1, i + 3)))
        return { kind: "manual", why: `leaf by \`${rest.slice(i, i + 3).join("; ")}\`` };
    }
  }
  return { kind: m[1] ? "budget" : "auto", steps: m[1] ? Number(m[1]) : null };
}

/**
 * The module's commands: each starts at a column-0 line outside a comment
 * and runs to the next one, so a statement or a body is never cut short or
 * run on into the next declaration.
 */
export function commands(src) {
  const out = [];
  let depth = 0;
  for (const line of src.split("\n")) {
    const start = depth === 0 && /^\S/.test(line) && !line.startsWith("--");
    if (start) out.push([line]);
    else if (out.length > 0) out[out.length - 1].push(line);
    for (let k = 0; k < line.length; k++) {
      if (line.startsWith("/-", k)) { depth++; k++; }
      else if (depth > 0 && line.startsWith("-/", k)) { depth--; k++; }
      else if (depth === 0 && line.startsWith("--", k)) break;
    }
  }
  return out;
}

/**
 * Every `theorem … := by` and `sol_auto_theorem` of a module: its name, its
 * body's lines (trimmed, line comments dropped; a block comment in a body
 * makes it manual), and the `set_option … in` that precedes it, if any.
 */
export function proofs(src) {
  const out = [];
  let opts = null;
  for (const cmd of commands(src)) {
    const head = cmd[0];
    if (head.startsWith("/-")) continue;
    if (head.startsWith("set_option ")) { opts = head; continue; }
    const name = (n) => n.replace(/\.(proved|refuted)$/, "").split(".").pop();
    const kind = (n) => (n.endsWith(".refuted") ? "refuted" : "proved");
    const a = head.match(/^sol_auto_theorem (\S+)/);
    const t = head.match(/^theorem (\S+)/);
    if (a) {
      const rest = cmd.slice(1).map((l) => l.replace(/--.*$/, "").trim()).filter(Boolean);
      const body = rest.length === 0 && !/:=/.test(head) ? ["sol_auto"] : ["sol_auto_theorem with a proof"];
      out.push({ name: name(a[1]), kind: kind(a[1]), body, opts });
    } else if (t) {
      const text = cmd.join("\n");
      const k = text.indexOf(":= by");
      const after = k < 0 ? "" : text.slice(k + 5);
      const body = k < 0 ? ["(no tactic proof)"] : after.includes("/-") ? ["(a comment in the proof)"]
        : after.split("\n").map((l) => l.replace(/--.*$/, "").trim()).filter(Boolean);
      out.push({ name: name(t[1]), kind: kind(t[1]), body, opts });
    }
    opts = null;
  }
  return out;
}

function main() {
  const counts = { auto: 0, budget: 0, manual: 0 };
  const findings = [];
  let refuted = 0;
  const modules = readdirSync(DIR).filter((f) => /^(Derived\d+|Refuted)\.lean$/.test(f)).sort();
  for (const f of modules) {
    for (const p of proofs(readFileSync(join(DIR, f), "utf8"))) {
      if (p.kind === "refuted") {
        // a refutation is automatic when it is `sol_refute` alone, in `Refuted.lean`
        refuted++;
        if (f !== "Refuted.lean" || p.opts || p.body.join("; ") !== "sol_refute") {
          counts.manual++;
          findings.push(`manual: ${f} ${p.name}: refuted by \`${p.body.join("; ")}\``);
        }
        continue;
      }
      let c = classify(p.body);
      if (p.opts) c = { kind: "manual", why: `\`${p.opts}\`` };
      counts[c.kind]++;
      if (c.kind === "manual") findings.push(`manual: ${f} ${p.name}: ${c.why}`);
    }
  }
  const report = readFileSync(join(DIR, "Report.lean"), "utf8");
  const pin = report.match(/(\d+) derived, (\d+) pending/);
  const pendingBlock = report.match(/^pending:\n([\s\S]*?)\n-\/$/m);
  const pending = pendingBlock ? pendingBlock[1].split(/\s+/).filter(Boolean) : [];
  const pinRefuted = (report.match(/^refuted \S+$/gm) ?? []).length;
  // the counts read here are the pin's, so no theorem is missed or counted twice
  if (!pin || counts.auto + counts.budget + counts.manual !== Number(pin[1]) ||
      Number(pin[2]) !== pending.length || refuted !== pinRefuted) {
    findings.push(`counts: ${counts.auto + counts.budget + counts.manual} proved and ${refuted} ` +
      `refuted read here, the pin has ${pin?.[1] ?? "?"} derived, ${pinRefuted} refuted, ` +
      `${pin?.[2] ?? "?"} pending (${pending.length} listed)`);
    counts.manual++;
  }
  let over = 0;
  if (buildLog) {
    const ts = timings(readFileSync(buildLog, "utf8"));
    for (const [m, t] of ts) {
      if (t > budget) {
        findings.push(`time: ${m} took ${t.toFixed(0)} s, past its ${budget} s budget`);
        over++;
      }
    }
    console.log(`check-automatic: ${ts.length} TestSuite modules timed, budget ${budget} s each`);
  }
  if (strict) for (const p of pending) findings.push(`pending: ${p}`);
  console.log(`check-automatic: ${counts.auto} automatic, ${counts.budget} with a step budget, ` +
    `${counts.manual} manual; ${refuted} refuted; ${pin ? pin[2] : "?"} pending`);
  for (const f of findings) console.log(`  ${f}`);
  const fail = counts.manual > 0 || over > 0 || (strict && findings.length > 0);
  process.exit(fail ? 1 : 0);
}

if (import.meta.url === `file://${process.argv[1]}`) main();
