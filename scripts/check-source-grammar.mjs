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
// - Each structured rule's constructors produce the rule's category (an
//   expression label an expression, a statement a statement, …).
// - Every `featureCtors`/`featureLexical`/`featureElsewhere` id is a manifest
//   feature, listed once; every manifest feature that cites the grammar or is
//   lexical has a row; every `Excl` has an id of scope `exclude`/`upstream`,
//   and every excluded or upstream-rejected feature is an `Excl` or is
//   decided elsewhere (`featureElsewhere`, with its stage).
// Comments in the Lean tables are blanked before they are read.
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
  if (start < 0) throw new Error(`no table ${name}`);
  const end = lean.indexOf("]\n", start);
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
// Comments dropped (the tables' strings hold no comment delimiters).
const uncomment = (t) => t.replace(/\/-[\s\S]*?-\//gu, "").replace(/--[^\n]*/gu, "");
const upstream = uncomment(read("Solidity/Source/Upstream.lean"));
const ctorRows = tableKeys(upstream, "grammarCtors");
const dataRows = tableKeys(upstream, "grammarData");
const featRows = tableKeys(upstream, "featureCtors");
const elsewhere = tableKeys(upstream, "featureElsewhere");
const lexical = [...(upstream.match(/def featureLexical[^\n]*:= \[([^\]]*)\]/u)?.[1] ?? "").matchAll(/"([^"]+)"/gu)].map((m) => m[1]);
const seen = new Map();
for (const { key } of [...ctorRows, ...dataRows]) seen.set(key, (seen.get(key) ?? 0) + 1);
for (const k of keys) if (!seen.has(k)) errors.push(`grammar ${k} is in neither grammarCtors nor grammarData`);
for (const [k, n] of seen) {
  if (!keys.has(k)) errors.push(`table key ${k} is not a rule or label of the grammar`);
  if (n > 1) errors.push(`grammar ${k} appears ${n} times in the tables`);
}
const syntax = blankLean(read("Solidity/Source/Syntax.lean"));
const synBody = syntax.slice(syntax.indexOf("inductive Syn :"), syntax.indexOf("end Solidity.Source"));
// Each constructor with its signature (continuation lines joined).
const sigs = new Map();
{
  let cur = null;
  for (const line of synBody.split("\n").slice(1)) {
    const m = line.match(/^ {2}\| (\w+)(.*)$/u);
    if (m) { cur = m[1]; sigs.set(cur, m[2]); }
    else if (cur && /^ {6}/u.test(line)) sigs.set(cur, sigs.get(cur) + " " + line.trim());
    else cur = null;
  }
}
const ctors = new Set(sigs.keys());
const resultCat = (k) => ((sigs.get(k) ?? "").match(/Syn [^:→]*$/u)?.[0] ?? "").trim();
// The category a row's constructors must produce, by rule.
const expectCat = (key) => key === "expression" || key.startsWith("expression#") || ["tupleExpression", "inlineArrayExpression",
  "literal", "literalWithSubDenomination"].includes(key) ? /Syn \.expr$/u
  : key.startsWith("yul") ? /Syn \.yul/u
  : ["simpleStatement", "variableDeclarationStatement", "variableDeclarationTuple", "expressionStatement"].includes(key) ? /Syn (\.simple|\(\.stmt)/u
  : /Statement$/u.test(key) ? /Syn \(\.stmt/u
  : /(contract|interface|library)Definition$/u.test(key) ? /Syn \.top$/u
  : /Definition$/u.test(key) || key === "stateVariableDeclaration" || key === "constantVariableDeclaration" ? /Syn (\(\.part|\.fallbackSig)/u
  : null;
for (const { key, value } of ctorRows) {
  const want = expectCat(key);
  if (!want) continue;
  for (const m of value.matchAll(/\.(\w+)/gu))
    if (!want.test(resultCat(m[1]))) errors.push(`${key}: .${m[1]} produces ${resultCat(m[1])}, not the rule's category`);
}
for (const { key, value } of [...ctorRows, ...featRows])
  for (const m of value.matchAll(/\.(\w+)/gu)) if (!ctors.has(m[1])) errors.push(`${key}: .${m[1]} is not a Syn constructor`);
const features = new Map(manifest.features.map((f) => [f.id, f]));
for (const id of [...featRows.map((r) => r.key), ...lexical]) if (!features.has(id)) errors.push(`feature ${id} is not in the manifest`);
const mapped = new Set([...featRows.map((r) => r.key), ...lexical]);
const elseIds = new Map(elsewhere.map((r) => [r.key, r.value.replaceAll('"', "")]));
const counts = new Map();
for (const id of [...featRows.map((r) => r.key), ...lexical, ...elseIds.keys()]) counts.set(id, (counts.get(id) ?? 0) + 1);
for (const [id, n] of counts) if (n > 1) errors.push(`feature ${id} appears ${n} times in featureCtors/featureLexical/featureElsewhere`);
for (const [id, stage] of elseIds) {
  if (!features.has(id)) errors.push(`featureElsewhere ${id} is not in the manifest`);
  if (!["S00", "S01", "S04.02", "G01", "G08"].includes(stage)) errors.push(`featureElsewhere ${id}: unknown stage ${stage}`);
}
const syntaxFeature = (f) => (f.upstream ?? []).some((u) => /docs\/grammar\/Solidity(Parser|Lexer)\.g4/u.test(u.path)) || f.category === "lexical";
for (const f of manifest.features)
  if (syntaxFeature(f) && !mapped.has(f.id) && !elseIds.has(f.id))
    errors.push(`manifest feature ${f.id} cites the grammar or is lexical but has no featureCtors/featureLexical/featureElsewhere row`);
const ctorLean = uncomment(read("Solidity/Source/Ctor.lean"));
const exclBody = ctorLean.slice(ctorLean.indexOf("inductive Excl where"), ctorLean.indexOf("deriving", ctorLean.indexOf("inductive Excl where")));
const exclCtors = [...exclBody.matchAll(/\| (\w+)/gu)].map((m) => m[1]);
const idBody = ctorLean.slice(ctorLean.indexOf("def Excl.id"), ctorLean.indexOf("\n\n", ctorLean.indexOf("def Excl.id")));
const exclIds = new Map([...idBody.matchAll(/\| \.(\w+) => "(\w+)"/gu)].map((m) => [m[1], m[2]]));
for (const k of exclCtors) if (!exclIds.has(k)) errors.push(`Excl.${k} has no Excl.id`);
for (const [k, id] of exclIds) {
  const f = features.get(id);
  if (!f || !["exclude", "upstream"].includes(f.scope)) errors.push(`Excl.id ${k} = ${id} is not an excluded or upstream-rejected feature`);
}
const decided = new Set([...exclIds.values(), ...elseIds.keys(), ...lexical]);
for (const f of manifest.features)
  if (["exclude", "upstream"].includes(f.scope) && !decided.has(f.id))
    errors.push(`excluded feature ${f.id} is neither an Excl nor in featureElsewhere`);
for (const e of errors) console.log(e);
console.log(`source-grammar: ${keys.size} rules and labels, ${ctorRows.length} constructor rows, ${dataRows.length} data rows, ${ctors.size} constructors, ${featRows.length + lexical.length} syntax features, ${exclIds.size} exclusions, ${elseIds.size} decided elsewhere; ${errors.length} errors`);
process.exit(errors.length ? 1 : 0);
