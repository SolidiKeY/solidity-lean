#!/usr/bin/env node
// Guard regression: pin relocation drops exact axiom guards or their multiplicity.
// Inventory only. It never edits files and does not certify a relocation.
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { lstatSync, readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { pins } from "../../check-axiom-pins.mjs";
import { blankLean } from "../../check-trust.mjs";

export function area(file) {
  const parts = file.split("/");
  return parts.length > 2 ? parts.slice(0, 2).join("/") : parts[0];
}

export function inventory(files) {
  const areas = {}, rows = [], keys = new Map();
  for (const { file, text } of files) {
    const found = pins(text);
    if (!found.length) continue;
    const hash = createHash("sha256").update(text).digest("hex");
    const name = area(file);
    areas[name] ??= { files: 0, occurrences: 0, unparsed_axioms: 0 };
    areas[name].files++;
    const matches = [...blankLean(text).matchAll(/#guard_msgs\s*(?:\([^)]*\)\s*)?in\s+#print\s+axioms\s+(\S+)/gu)];
    if (matches.length !== found.length) throw new Error(`scanner mismatch: ${file}`);
    for (const [index, pin] of found.entries()) {
      const match = matches[index];
      const before = text.slice(0, match.index).replace(/\s+$/u, "");
      const start = before.endsWith("-/") ? before.lastIndexOf("/--") : -1;
      const blockStart = start >= 0 && !before.slice(start + 3, -2).includes("-/") ? start : match.index;
      const block = text.slice(blockStart, match.index + match[0].length);
      const key = `${file}:${pin.name}`;
      keys.set(key, (keys.get(key) ?? 0) + 1);
      areas[name].occurrences++;
      if (pin.axioms === null) areas[name].unparsed_axioms++;
      rows.push({ file, source_sha256: hash, ...pin, old_checker_key: key,
                  start_byte: Buffer.byteLength(text.slice(0, blockStart)),
                  end_byte: Buffer.byteLength(text.slice(0, match.index + match[0].length)),
                  observed_block: block, block_sha256: createHash("sha256").update(block).digest("hex"),
                  suggested_destination: `${name}/AxiomPins.lean`,
                  suggested_new_key: `${name}/AxiomPins.lean:${pin.name}`,
                  destination: null, relocation: "unresolved" });
    }
  }
  const proposed = new Map();
  for (const row of rows) proposed.set(row.suggested_new_key, (proposed.get(row.suggested_new_key) ?? 0) + 1);
  return { areas, occurrences: rows.length, duplicate_checker_keys: [...keys].filter(([, n]) => n > 1),
           duplicate_suggested_keys: [...proposed].filter(([, n]) => n > 1), rows };
}

export function main() {
  const root = resolve(dirname(fileURLToPath(import.meta.url)), "../../..");
  const names = execFileSync("git", ["ls-files", "-z", "--", "Solidity", "Bridge", "tests"], { cwd: root }).toString("utf8").split("\0").filter(Boolean)
    .filter(p => p.endsWith(".lean") && !p.startsWith("Solidity/Scratch/"));
  const files = names.map(file => {
    const path = resolve(root, file);
    if (!lstatSync(path).isFile()) throw new Error(`nonregular source: ${file}`);
    const bytes = readFileSync(path);
    const text = bytes.toString("utf8");
    if (!Buffer.from(text).equals(bytes)) throw new Error(`invalid UTF-8 source: ${file}`);
    return { file, text };
  });
  const result = inventory(files);
  const required = JSON.parse(readFileSync(resolve(root, "scripts/g07-baseline.json"), "utf8")).requiredPins;
  if (!Array.isArray(required)) throw new Error("requiredPins missing");
  const present = new Set(result.rows.map(r => r.name));
  const missing = required.filter(n => !present.has(n));
  console.log(JSON.stringify({ status: "dry-run-inventory-not-migration", source_head_unverified: execFileSync("git", ["rev-parse", "HEAD"], {cwd: root, encoding:"utf8"}).trim(),
    scanner: "check-axiom-pins.mjs pins; tracked Lean files in Solidity, Bridge and tests", coverage: "parser-and-worktree-unverified", required_pin_names: required.length,
    missing_required_names: missing, ...result }, null, 2));
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try { main(); } catch (e) { console.error(`pin dry run failed: ${e.message}`); process.exitCode = 1; }
}
