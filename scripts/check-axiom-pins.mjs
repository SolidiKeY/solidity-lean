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
// - a new pin, or one whose set shrank, is reported until `--write` records it.
//
// Usage: node scripts/check-axiom-pins.mjs [--write]
// Exit 0 = inventory matches, 1 = drift or a non-standard axiom.
import { readFileSync, writeFileSync, readdirSync, statSync, existsSync } from "node:fs";
import { join, resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";

export const STANDARD = ["propext", "Classical.choice", "Quot.sound"];
const INVENTORY = "scripts/g07-axiom-pins.json";

// Pins in one file: [{ name, axioms }]; `name` as printed (fully qualified).
export function pins(text) {
  const out = [];
  const re = /\/--([\s\S]*?)-\/\s*#guard_msgs\s+in\s+#print\s+axioms\s+(\S+)/gu;
  for (const m of text.matchAll(re)) {
    const doc = m[1].replace(/\s+/gu, " ");
    const dep = doc.match(/'(\S+)' depends on axioms: \[([^\]]*)\]/u);
    const none = doc.match(/'(\S+)' does not depend on any axioms/u);
    if (dep) out.push({ name: dep[1], axioms: dep[2].split(",").map((a) => a.trim()).filter(Boolean).sort() });
    else if (none) out.push({ name: none[1], axioms: [] });
    else out.push({ name: m[2], axioms: null });
  }
  return out;
}

// Compare the found pins with the recorded inventory.
export function compare(found, recorded) {
  const errors = [], notes = [];
  for (const [name, { axioms, file }] of found) {
    if (axioms === null) { errors.push(`${file}: pin of ${name} prints no axiom line`); continue; }
    const extra = axioms.filter((a) => !STANDARD.includes(a));
    if (extra.length) errors.push(`${file}: ${name} depends on non-standard axioms ${extra.join(", ")}`);
    const old = recorded[name];
    if (!old) notes.push(`new pin ${name} [${axioms.join(", ")}]`);
    else {
      const grown = axioms.filter((a) => !old.includes(a));
      if (grown.length) errors.push(`${file}: ${name} gained ${grown.join(", ")} (recorded [${old.join(", ")}])`);
      else if (axioms.length < old.length) notes.push(`pin ${name} shrank to [${axioms.join(", ")}]`);
    }
  }
  for (const name of Object.keys(recorded)) if (!found.has(name)) errors.push(`recorded pin ${name} is gone`);
  return { errors, notes };
}

export function collect(root) {
  const files = [];
  (function walk(dir) {
    for (const f of readdirSync(join(root, dir)).sort()) {
      const p = dir ? join(dir, f) : f;
      if (p === "Solidity/Scratch" || p.startsWith(".") || p === "vendor" || p === "node_modules") continue;
      if (statSync(join(root, p)).isDirectory()) { if (!dir && !["Solidity", "Bridge", "tests"].includes(p)) continue; walk(p); }
      else if (p.endsWith(".lean")) files.push(p);
    }
  })("");
  const found = new Map();
  for (const file of files) for (const pin of pins(readFileSync(join(root, file), "utf8")))
    found.set(pin.name, { axioms: pin.axioms, file });
  return found;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
  const found = collect(root);
  const path = join(root, INVENTORY);
  if (process.argv.includes("--write")) {
    const obj = Object.fromEntries([...found].sort(([a], [b]) => a.localeCompare(b)).map(([n, { axioms }]) => [n, axioms]));
    writeFileSync(path, JSON.stringify(obj, null, 1) + "\n");
  }
  const recorded = existsSync(path) ? JSON.parse(readFileSync(path, "utf8")) : {};
  const { errors, notes } = compare(found, recorded);
  for (const e of errors) console.log(`ERROR  ${e}`);
  for (const n of notes) console.log(`NOTE   ${n}`);
  const counts = {};
  for (const { axioms } of found.values()) { const k = `[${(axioms ?? ["?"]).join(", ")}]`; counts[k] = (counts[k] ?? 0) + 1; }
  console.log(`axiom-pins: ${found.size} pinned theorems ${JSON.stringify(counts)}, ${errors.length} errors, ${notes.length} unrecorded changes`);
  process.exit(errors.length || notes.length ? 1 : 0);
}
