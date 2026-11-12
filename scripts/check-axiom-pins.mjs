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
import { readFileSync, writeFileSync, readdirSync, statSync, lstatSync, existsSync, mkdirSync, unlinkSync } from "node:fs";
import { join, resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
import { isDeepStrictEqual } from "node:util";
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

// Seeded legacy fragments retain their paths/bytes; new sources use neutral hashes.
export const FRAGMENTS = "scripts/g07-axiom-pins.d";
export const CANONICAL_FRAGMENTS = "scripts/axiom-pins";
export const fragmentRoots = [FRAGMENTS, CANONICAL_FRAGMENTS];

export function parseUnique(text, label = "JSON") {
  const obj = JSON.parse(text); // Validate syntax before scanning decoded object keys.
  const stack = [];
  for (const m of text.matchAll(/"(?:\\[\s\S]|[^"\\])*"|[{}\[\]]/gu)) {
    const t = m[0];
    if (t === "{") stack.push(new Set());
    else if (t === "[") stack.push(null);
    else if (t === "}" || t === "]") stack.pop();
    else {
      let next = m.index + t.length;
      while (next < text.length && /\s/u.test(text[next])) next++;
      if (text[next] !== ":") continue;
      const key = JSON.parse(t), keys = stack.at(-1);
      if (keys.has(key)) throw new Error(`${label}: duplicate key ${key}`);
      keys.add(key);
    }
  }
  return obj;
}

export function pinSource(key) {
  const i = key.indexOf(".lean:");
  const source = key.slice(0, i + 5), name = key.slice(i + 6);
  if (i <= 0 || !name || /[\\\0\r\n]/u.test(source) ||
      source.split("/").some(p => !p || p === "." || p === ".."))
    throw new Error(`malformed pin key: ${key}`);
  return source;
}

export function validatePinObject(obj, label = "inventory") {
  if (!obj || Array.isArray(obj) || typeof obj !== "object") throw new Error(`${label}: not an object`);
  for (const [key, axioms] of Object.entries(obj)) {
    pinSource(key);
    if (!Array.isArray(axioms) || !axioms.every(a => typeof a === "string"))
      throw new Error(`${label}: invalid axiom list: ${key}`);
    if (axioms.some(a => !STANDARD.includes(a))) throw new Error(`${label}: non-standard axiom: ${key}`);
  }
  return obj;
}

export function legacyPaths(root, revision = null) {
  const run = args => execFileSync("git", args, { cwd: root, encoding: "utf8" });
  const historical = revision && run(["ls-tree", "--name-only", revision, "--", "scripts/hygiene/allow.json"]).trim();
  // A merge base may predate the policy file that names the immutable seed.
  // Present historical policy is still parsed strictly; only absence falls back.
  const raw = historical ? run(["show", `${revision}:scripts/hygiene/allow.json`]) :
    readFileSync(join(root, "scripts/hygiene/allow.json"), "utf8");
  const { seed } = parseUnique(raw, "hygiene seed");
  if (!/^[0-9a-f]{40}$/u.test(seed ?? "")) throw new Error("invalid immutable hygiene seed");
  return new Set(run(["ls-tree", "-r", "--name-only", "-z", seed, "--", FRAGMENTS]).split("\0").filter(Boolean));
}

export const sourceDigest = source => createHash("sha256").update(source, "utf8").digest("hex");
export function fragmentPath(source, eligible, digest = sourceDigest) {
  const legacy = `${FRAGMENTS}/${source.slice(0, -5)}.json`;
  return eligible.has(legacy) ? legacy : `${CANONICAL_FRAGMENTS}/${digest(source)}.json`;
}

export function readFragmentFiles(root) {
  const files = {};
  function walk(relative) {
    const full = join(root, relative);
    const st = lstatSync(full, { throwIfNoEntry: false });
    if (!st) return;
    if (st.isSymbolicLink()) throw new Error(`unexpected symbolic fragment path: ${relative}`);
    if (st.isDirectory()) for (const name of readdirSync(full).sort()) walk(`${relative}/${name}`);
    else {
      if (!relative.endsWith(".json") || !st.isFile()) throw new Error(`unexpected fragment file: ${relative}`);
      files[relative] = readFileSync(full, "utf8");
    }
  }
  for (const relative of fragmentRoots) {
    const segments = relative.split("/");
    for (let i = 1; i < segments.length; i++) {
      const parent = segments.slice(0, i).join("/");
      if (lstatSync(join(root, parent), { throwIfNoEntry: false })?.isSymbolicLink())
        throw new Error(`unexpected symbolic fragment path: ${parent}`);
    }
    walk(relative);
  }
  return files;
}

export function validateFragments(files, eligible, digest = sourceDigest) {
  const parts = {}, merged = {}, owners = new Map();
  for (const [file, raw] of Object.entries(files)) {
    if (!fragmentRoots.some(d => file.startsWith(d + "/")) || !file.endsWith(".json"))
      throw new Error(`unexpected fragment file: ${file}`);
    const part = validatePinObject(parseUnique(raw, file), file);
    const sources = new Set();
    for (const [key, value] of Object.entries(part)) {
      sources.add(pinSource(key));
      if (owners.has(key)) throw new Error(`duplicate across fragments: ${key} in ${owners.get(key)} and ${file}`);
      owners.set(key, file); merged[key] = value;
    }
    if (sources.size > 1) throw new Error(`${file}: mixed source fragment`);
    if (!sources.size && !eligible.has(file)) throw new Error(`${file}: unrecognized empty fragment`);
    parts[file] = part;
  }
  for (const [file, part] of Object.entries(parts)) for (const key of Object.keys(part)) {
    const expected = fragmentPath(pinSource(key), eligible, digest);
    if (file !== expected) throw new Error(`wrong fragment: ${key} in ${file}; expected ${expected}`);
  }
  return { parts, merged };
}

export function groupFragments(obj, eligible, digest = sourceDigest) {
  validatePinObject(obj);
  const parts = {}, sources = new Map();
  for (const [key, axioms] of Object.entries(obj)) {
    const source = pinSource(key), file = fragmentPath(source, eligible, digest);
    if (sources.has(file) && sources.get(file) !== source) throw new Error(`fragment hash collision: ${file}`);
    sources.set(file, source); parts[file] ??= {}; parts[file][key] = axioms;
  }
  return parts;
}

export const compactInventory = obj => JSON.stringify(Object.fromEntries(
  Object.entries(obj).sort(([a], [b]) => a.localeCompare(b)))) + "\n";

export function planFragments(files, obj, eligible, digest = sourceDigest) {
  const current = validateFragments(files, eligible, digest), parts = groupFragments(obj, eligible, digest);
  const writes = {};
  for (const [file, part] of Object.entries(parts)) {
    if (isDeepStrictEqual(part, current.parts[file])) continue; // Preserve raw legacy bytes.
    writes[file] = JSON.stringify(Object.fromEntries(Object.entries(part).sort(([a], [b]) => a.localeCompare(b))), null, 1) + "\n";
  }
  return { writes, deletes: Object.keys(current.parts).filter(file => !Object.hasOwn(parts, file)) };
}

export function writeFragments(root, obj) {
  // Validate the complete old/new state before writing or pruning any file.
  const plan = planFragments(readFragmentFiles(root), obj, legacyPaths(root));
  for (const [file, raw] of Object.entries(plan.writes)) {
    mkdirSync(dirname(join(root, file)), { recursive: true }); writeFileSync(join(root, file), raw);
  }
  for (const file of plan.deletes) unlinkSync(join(root, file));
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

const main = process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url);
// Shared storage validation/planning for the Python fragment generator and census.
if (main && process.argv.includes("--fragment-op")) {
  try {
    const input = parseUnique(readFileSync(0, "utf8"), "fragment request");
    const root = resolve(input.root);
    if (input.op === "objects") {
      for (const obj of input.objects) validatePinObject(obj);
      process.stdout.write("{}\n");
    } else {
      const eligible = legacyPaths(root, input.revision ?? null);
      const files = input.files ?? readFragmentFiles(root);
      const result = input.op === "plan" ? planFragments(files, input.desired, eligible) :
        input.op === "validate" ? validateFragments(files, eligible) : (() => { throw new Error("unknown fragment operation"); })();
      process.stdout.write(JSON.stringify(result) + "\n");
    }
  } catch (error) { console.error(`fragments: ${error.message}`); process.exit(2); }
} else if (main) {
  const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
  const found = collect(root);
  const path = join(root, INVENTORY);
  if (process.argv.includes("--write")) {
    const obj = Object.fromEntries([...found].sort(([a], [b]) => a.localeCompare(b)).map(([n, { axioms }]) => [n, axioms]));
    writeFragments(root, obj);
    writeFileSync(path, compactInventory(obj));
  }
  const recorded = existsSync(path) ? validatePinObject(parseUnique(readFileSync(path, "utf8"), INVENTORY)) : {};
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
