#!/usr/bin/env node
// Roadmap G07: the axiom inventory of every `#guard_msgs`-pinned
// `#print axioms` in the tracked Lean sources
// (docs/feature-work/roadmap-g07-gates.md, "Axiom inventory").
//
// Lean checks each pin when it builds the file; this gate checks the pins
// themselves against `scripts/g07-axiom-pins.json`:
// - a pinned theorem may depend only on `propext`, `Classical.choice` and
//   `Quot.sound` (a pin that records `sorryAx` or a new axiom still passes
//   `#guard_msgs`, so the build alone does not catch it);
// - a recorded pin may not disappear and its axiom set may not grow;
// - a new pin, or one whose set shrank, is reported until `--write` records it,
//   except exact H112 historical changes in the SHA-pinned shrink-only baseline.
//   Baseline matching never suppresses any error above.
//
// Usage: node scripts/check-axiom-pins.mjs [--write]
// Exit 0 = inventory matches, 1 = drift or a non-standard axiom.
import { readFileSync, writeFileSync, readdirSync, statSync, existsSync, mkdirSync, rmdirSync, unlinkSync } from "node:fs";
import { join, resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import { blankLean } from "./check-trust.mjs";
import { loadDriftBaseline, changeKey } from "./axiom-pin-drift-baseline.mjs";

export const STANDARD = ["propext", "Classical.choice", "Quot.sound"];
const INVENTORY = "scripts/g07-axiom-pins.json";

// Pins in one file: [{ name, target, axioms }]. A pin is a
// `#guard_msgs (opts)? in #print axioms X` outside comments, with the doc
// comment that ends right before it; `name` is the printed name, which must
// end with `X`.
export function pins(text) {
  const out = [];
  const clean = blankLean(text);
  const re = /#guard_msgs\s*(?:\([^)]*\)\s*)?in\s+#print\s+axioms\s+(\S+)/gu;
  for (const m of clean.matchAll(re)) {
    const before = text.slice(0, m.index).replace(/\s+$/u, "");
    let doc = null;
    if (before.endsWith("-/")) {
      const start = before.lastIndexOf("/--");
      const body = start < 0 ? null : before.slice(start + 3, -2);
      if (body !== null && !body.includes("-/")) doc = body.replace(/\s+/gu, " ");
    }
    const dep = doc?.match(/'(\S+)' depends on axioms: \[([^\]]*)\]/u);
    const none = doc?.match(/'(\S+)' does not depend on any axioms/u);
    const target = m[1];
    if (dep) out.push({ name: dep[1], target, axioms: dep[2].split(",").map((a) => a.trim()).filter(Boolean).sort() });
    else if (none) out.push({ name: none[1], target, axioms: [] });
    else out.push({ name: target, target, axioms: null });
  }
  return out;
}

// Compare the found pins with the recorded inventory.
export function compare(found, recorded) {
  const errors = [], notes = [], changes = [];
  for (const [key, { name, target, axioms, file }] of found) {
    if (axioms === null) { errors.push(`${file}: pin of ${name} prints no axiom line`); continue; }
    if (target && name !== target && !name.endsWith("." + target)) errors.push(`${file}: pin of ${target} prints ${name}`);
    const extra = axioms.filter((a) => !STANDARD.includes(a));
    if (extra.length) errors.push(`${file}: ${name} depends on non-standard axioms ${extra.join(", ")}`);
    const old = recorded[key];
    if (!old) {
      notes.push(`new pin ${name} [${axioms.join(", ")}]`);
      changes.push({ key, kind: "new", recorded: null, axioms: [...axioms].sort() });
    }
    else {
      const grown = axioms.filter((a) => !old.includes(a));
      if (grown.length) errors.push(`${file}: ${name} gained ${grown.join(", ")} (recorded [${old.join(", ")}])`);
      else if (axioms.length < old.length) {
        notes.push(`pin ${name} shrank to [${axioms.join(", ")}]`);
        changes.push({ key, kind: "shrunk", recorded: [...old].sort(), axioms: [...axioms].sort() });
      }
    }
  }
  for (const key of Object.keys(recorded)) if (!found.has(key)) errors.push(`recorded pin ${key} is gone`);
  return { errors, notes, changes };
}

// The inventory is generated from one fragment per Lean file,
// `scripts/g07-axiom-pins.d/<file without .lean>.json`, holding that file's
// pins (`scripts/coord-tools/fragments.sh`); `--write` rewrites both.
export const FRAGMENTS = "scripts/g07-axiom-pins.d";
export function writeFragments(root, obj) {
  const parts = new Map();
  for (const [key, axioms] of Object.entries(obj)) {
    const i = key.indexOf(".lean:");
    const f = `${FRAGMENTS}/${key.slice(0, i)}.json`;
    if (!parts.has(f)) parts.set(f, {});
    parts.get(f)[key] = axioms;
  }
  const dir = join(root, FRAGMENTS);
  (function prune(d) {
    if (!existsSync(d)) return;
    for (const f of readdirSync(d)) {
      const p = join(d, f);
      if (statSync(p).isDirectory()) { prune(p); if (!readdirSync(p).length) rmdirSync(p); }
      else if (!parts.has(p.slice(root.length + 1))) unlinkSync(p);
    }
  })(dir);
  for (const [f, part] of parts) {
    mkdirSync(dirname(join(root, f)), { recursive: true });
    writeFileSync(join(root, f), JSON.stringify(part, null, 1) + "\n");
  }
}

export function collect(root) {
  const files = [];
  (function walk(dir) {
    for (const f of readdirSync(join(root, dir)).sort()) {
      const p = dir ? join(dir, f) : f;
      if (f === ".lake" || p === "Solidity/Scratch" || p.startsWith(".") || p === "vendor" || p === "node_modules") continue;
      if (statSync(join(root, p)).isDirectory()) { if (!dir && !["Solidity", "Bridge", "tests"].includes(p)) continue; walk(p); }
      else if (p.endsWith(".lean")) files.push(p);
    }
  })("");
  const found = new Map();
  for (const file of files) for (const pin of pins(readFileSync(join(root, file), "utf8")))
    found.set(`${file}:${pin.name}`, { ...pin, file });
  return found;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
  const found = collect(root);
  const path = join(root, INVENTORY);
  if (process.argv.includes("--write")) {
    const obj = Object.fromEntries([...found].sort(([a], [b]) => a.localeCompare(b)).map(([n, { axioms }]) => [n, axioms]));
    writeFileSync(path, JSON.stringify(obj, null, 1) + "\n");
    writeFragments(root, obj);
  }
  const recorded = existsSync(path) ? JSON.parse(readFileSync(path, "utf8")) : {};
  const { errors, notes, changes } = compare(found, recorded);
  let allowed = new Set();
  try { allowed = loadDriftBaseline(root, STANDARD); }
  catch (error) { errors.push(`pin drift baseline: ${error.message}`); }
  const pending = changes.map((change,index) => ({change,note:notes[index]})).filter(({change})=>!allowed.has(changeKey(change)));
  for (const e of errors) console.log(`ERROR  ${e}`);
  for (const {note} of pending) console.log(`NOTE   ${note}`);
  const counts = {};
  for (const { axioms } of found.values()) { const k = `[${(axioms ?? ["?"]).join(", ")}]`; counts[k] = (counts[k] ?? 0) + 1; }
  console.log(`axiom-pins: ${found.size} pinned theorems ${JSON.stringify(counts)}, ${errors.length} errors, ${pending.length} unrecorded changes, ${changes.length-pending.length} baselined changes`);
  process.exit(errors.length || pending.length ? 1 : 0);
}
