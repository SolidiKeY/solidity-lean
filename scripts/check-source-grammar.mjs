#!/usr/bin/env node
// Roadmap S00: the source syntax against the pinned grammar and the manifest
// (docs/feature-work/source-s00-s01.md, "Upstream mapping").
//
// - The vendored grammar (`tests/upstream/grammar-0.8.38/*.g4`) has the
//   SHA-256 hashes G00 pinned in `docs/solidity-features.json`.
// - Every parser rule and every labelled alternative (`rule#Label`) is a key
//   of exactly one of `grammarCtors` and `grammarData`
//   (`Solidity/Source/Upstream.lean`); every key is a rule or label.
// - Every constructor named in `grammarCtors`/`featureCtors` is a `Syn`
//   constructor (`Solidity/Source/Syntax.lean`); Lean checks the converse
//   (`Ctor.grammar_covers`).
// - Every `featureCtors`/`featureLexical` id is a manifest feature, and every
//   manifest feature that cites the parser grammar is one of them; every
//   `Excl.id` is a feature of scope `exclude` or `upstream`.
//
// Usage: node scripts/check-source-grammar.mjs
// Exit 0 = consistent, 1 = a mismatch (each printed).
import { readFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import { blankLean } from "./check-trust.mjs";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const read = (p) => readFileSync(resolve(root, p), "utf8");

export function grammarKeys(g4) {
  const text = g4.replace(/\/\*[\s\S]*?\*\//gu, "").replace(/\/\/[^\n]*/gu, "");
  const rules = [...text.matchAll(/^([a-z]\w*)\s*(?:\[[^\]]*\])?\s*(?:\n\s*)?(?:locals\s*\[[^\]]*\]\s*)?:/gmu)].map((m) => m[1]);
  const keys = new Set(rules);
  // Labels: `# Label` inside a rule body; the rule is the nearest one above.
  let current = null;
  for (const line of text.split("\n")) {
    const r = line.match(/^([a-z]\w*)\b/u);
    if (r && rules.includes(r[1])) current = r[1];
    for (const m of line.matchAll(/#\s*([A-Z]\w*)/gu)) keys.add(`${current}#${m[1]}`);
  }
  return keys;
}

const tableKeys = (lean, name) => {
  const start = lean.indexOf(`def ${name} :`);
  const end = lean.indexOf("\n\n", start);
  const body = lean.slice(start, end);
  return [...body.matchAll(/\("([^"]+)",\s*(\[[^\]]*\]|"[^"]*")\)/gu)].map((m) => ({ key: m[1], value: m[2] }));
};

const errors = [];
const manifest = JSON.parse(read("docs/solidity-features.json"));
for (const f of ["SolidityParser.g4", "SolidityLexer.g4"]) {
  const pin = manifest.upstream.sources.find((s) => s.path === `docs/grammar/${f}`);
  const hash = createHash("sha256").update(readFileSync(resolve(root, "tests/upstream/grammar-0.8.38", f))).digest("hex");
  if (!pin) errors.push(`no G00 pin for docs/grammar/${f}`);
  else if (pin.sha256 !== hash) errors.push(`${f}: sha256 ${hash} differs from the G00 pin ${pin.sha256}`);
}
const keys = grammarKeys(read("tests/upstream/grammar-0.8.38/SolidityParser.g4"));
const upstream = read("Solidity/Source/Upstream.lean");
const ctorRows = tableKeys(upstream, "grammarCtors");
const dataRows = tableKeys(upstream, "grammarData");
const featRows = tableKeys(upstream, "featureCtors");
const lexical = [...(upstream.match(/def featureLexical[^\n]*:= \[([^\]]*)\]/u)?.[1] ?? "").matchAll(/"([^"]+)"/gu)].map((m) => m[1]);
const seen = new Map();
for (const { key } of [...ctorRows, ...dataRows]) seen.set(key, (seen.get(key) ?? 0) + 1);
for (const k of keys) if (!seen.has(k)) errors.push(`grammar ${k} is in neither grammarCtors nor grammarData`);
for (const [k, n] of seen) {
  if (!keys.has(k)) errors.push(`table key ${k} is not a rule or label of the grammar`);
  if (n > 1) errors.push(`grammar ${k} appears ${n} times in the tables`);
}
const syntax = blankLean(read("Solidity/Source/Syntax.lean"));
const synBody = syntax.slice(syntax.indexOf("inductive Syn :"));
const ctors = new Set([...synBody.matchAll(/^\s*\| (\w+)/gmu)].map((m) => m[1]));
for (const { key, value } of [...ctorRows, ...featRows])
  for (const m of value.matchAll(/\.(\w+)/gu)) if (!ctors.has(m[1])) errors.push(`${key}: .${m[1]} is not a Syn constructor`);
const features = new Map(manifest.features.map((f) => [f.id, f]));
for (const id of [...featRows.map((r) => r.key), ...lexical]) if (!features.has(id)) errors.push(`feature ${id} is not in the manifest`);
const mapped = new Set([...featRows.map((r) => r.key), ...lexical]);
for (const f of manifest.features)
  if ((f.upstream ?? []).some((u) => u.path === "docs/grammar/SolidityParser.g4") && !mapped.has(f.id))
    errors.push(`manifest feature ${f.id} cites the parser grammar but has no featureCtors/featureLexical row`);
const ctorLean = read("Solidity/Source/Ctor.lean");
for (const m of ctorLean.matchAll(/\| \.\w+ => "(\w+)"/gu)) {
  const f = features.get(m[1]);
  if (!f || !["exclude", "upstream"].includes(f.scope)) errors.push(`Excl.id ${m[1]} is not an excluded or upstream-rejected feature`);
}
for (const e of errors) console.log(e);
console.log(`source-grammar: ${keys.size} rules and labels, ${ctorRows.length} constructor rows, ${dataRows.length} data rows, ${ctors.size} constructors, ${featRows.length + lexical.length} features; ${errors.length} errors`);
process.exit(errors.length ? 1 : 0);
