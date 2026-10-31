#!/usr/bin/env node
// G08–G11: the checked frontend's tables against the pinned grammar
// (docs/feature-work/frontend-parse.md).
//
// - `lexRules` in Solidity/Frontend/Checked/LexExamples.lean names every
//   lexer rule of tests/upstream/grammar-0.8.38/SolidityLexer.g4 (fragments
//   excepted) exactly once; Lean proves each sample is classified as stated.
// - Solidity/Frontend/Checked/Tables.lean is what
//   scripts/checked-lexer-tables.py generates.
//
// Usage: node scripts/check-checked-frontend.mjs
// Exit 0 = consistent, 1 = a mismatch (printed).
import { readFileSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const read = (p) => readFileSync(resolve(root, p), "utf8");
let bad = 0;
const fail = (m) => { console.log(`MISMATCH ${m}`); bad++; };

const g4 = read("tests/upstream/grammar-0.8.38/SolidityLexer.g4")
  .split("\n").filter((l) => !l.trim().startsWith("//")).join("\n")
  .replace(/\/\*\*[\s\S]*?\*\//g, "");
const rules = [...g4.matchAll(/^([A-Za-z_]+)\s*:/gm)].map((m) => m[1]);
const lean = read("Solidity/Frontend/Checked/LexExamples.lean");
const table = lean.split("def lexRules")[1].split("\n]\n")[0];
const named = [...table.matchAll(/^\s*\("(\w+)",/gm)].map((m) => m[1]);
const count = (xs) => xs.reduce((m, x) => m.set(x, (m.get(x) ?? 0) + 1), new Map());
const cn = count(named);
for (const r of new Set(rules)) if (!cn.has(r)) fail(`lexer rule ${r} missing from lexRules`);
for (const [n, k] of cn) {
  if (!rules.includes(n)) fail(`lexRules names ${n}, not a lexer rule`);
  if (k > 1) fail(`lexRules names ${n} ${k} times`);
}

// The reserved keywords against `ReservedKeywords`.
const resG = new Set([...g4.split("ReservedKeywords:")[1].split(";")[0].matchAll(/'(\w+)'/g)].map((m) => m[1]));
const tokLean = read("Solidity/Frontend/Checked/Token.lean");
const resL = new Set([...tokLean.split("def reservedKeywords")[1].split("\n\n")[0].matchAll(/"(\w+)"/g)]
  .map((m) => m[1]));
for (const r of resG) if (!resL.has(r)) fail(`reserved keyword ${r} missing from reservedKeywords`);
for (const r of resL) if (!resG.has(r)) fail(`reservedKeywords has ${r}, not reserved by the grammar`);

const t = spawnSync("python3", [resolve(root, "scripts/checked-lexer-tables.py"), "--check"],
  { encoding: "utf8" });
if (t.status !== 0) fail(`Tables.lean: ${(t.stdout + t.stderr).trim()}`);

console.log(`checked frontend: ${new Set(rules).size} lexer rules, ${named.length} in lexRules, ` +
  `${resG.size} reserved keywords, ${bad} mismatches`);
process.exit(bad ? 1 : 0);
