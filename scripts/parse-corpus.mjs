#!/usr/bin/env node
// G11: run the checked parser (Solidity/Frontend/Checked) over solc 0.8.38's
// syntax tests and the repository's `.sol` files, and compare with solc's
// expectation (docs/feature-work/frontend-parse.md, "Corpus regression").
//
// A syntax test is expected to be refused when its expectations list a
// `ParserError` (solc's lexer errors are reported as parser errors) other than
// 6275 (an import source not found, the resolver's), and
// accepted otherwise (later errors, warnings, none). A test with several
// `==== Source: … ====` units is accepted when every unit is. Repository
// `.sol` files are expected accepted, except under `illegal/` or
// `nocompile/`. Every disagreement gets a reason from `rules`; the report
// fails on one without. Accepted units are also
// printed and parsed again (the round trip of the backfill item).
//
// Steps:
//   node scripts/parse-corpus.mjs prepare   extract the tarball, split units,
//                                           write .cache/parse-corpus/manifest.tsv
//   (Lean) elaborate scripts/ParseCorpus.lean from the repository root, in
//                                           the editor or Lean server, or
//                                           `lake env lean scripts/ParseCorpus.lean`:
//                                           writes .cache/parse-corpus/results.tsv
//   node scripts/parse-corpus.mjs report    counts and disagreements; with
//                                           --write records tests/parse-corpus/baseline.json,
//                                           otherwise compares with it (exit 1 on a change)
import { readFileSync, writeFileSync, mkdirSync, readdirSync, statSync, existsSync, rmSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { resolve, dirname, join, relative } from "node:path";
import { fileURLToPath } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const cache = resolve(root, ".cache/parse-corpus");
const baselinePath = resolve(root, "tests/parse-corpus/baseline.json");
const mode = process.argv[2];

function walk(dir, out = []) {
  for (const f of readdirSync(dir)) {
    const p = join(dir, f);
    if (statSync(p).isDirectory()) walk(p, out);
    else if (p.endsWith(".sol")) out.push(p);
  }
  return out;
}

// The units of a syntax test (split at `==== Source: name ====`) and its
// expectation.
function splitTest(text) {
  const [src, exp = ""] = text.split(/^\/\/ ----\s*$/m);
  // ParserError 6275 ("Source … not found") is the import resolver's, not
  // the grammar's: not a parse refusal.
  const codes = [...exp.matchAll(/^\/\/ ParserError (\d+)/gm)].map((m) => m[1]).filter((c) => c !== "6275");
  const expectRefuse = codes.length > 0;
  const parts = src.split(/^==== Source: (.*) ====\s*$/m);
  const units = [];
  if (parts.length === 1) units.push(["main", parts[0]]);
  else {
    if (parts[0].trim() !== "") units.push(["main", parts[0]]);
    for (let i = 1; i < parts.length; i += 2) units.push([parts[i], parts[i + 1]]);
  }
  return { expectRefuse, codes, units };
}

if (mode === "prepare") {
  rmSync(cache, { recursive: true, force: true });
  mkdirSync(join(cache, "units"), { recursive: true });
  mkdirSync(join(cache, "solc"), { recursive: true });
  const t = spawnSync("tar", ["xzf", resolve(root, "tests/upstream/solidity-0.8.38.tar.gz"), "-C",
    join(cache, "solc"), "test/libsolidity/syntaxTests"], { encoding: "utf8" });
  if (t.status !== 0) { console.error(t.stderr); process.exit(2); }
  const rows = [];
  let n = 0;
  const add = (id, expect, name, body, codes = []) => {
    const f = join(cache, "units", `${n++}.sol`);
    writeFileSync(f, body, "latin1");
    rows.push([expect, id, name, relative(root, f), codes.join(",")].join("\t"));
  };
  for (const p of walk(join(cache, "solc/test/libsolidity/syntaxTests")).sort()) {
    const { expectRefuse, codes, units } = splitTest(readFileSync(p, "latin1"));
    const id = "solc:" + relative(join(cache, "solc/test/libsolidity/syntaxTests"), p);
    for (const [name, body] of units) add(id, expectRefuse ? "refuse" : "accept", name, body, codes);
  }
  for (const p of walk(resolve(root, "tests")).sort()) {
    if (p.startsWith(cache)) continue;
    // The repository's own negative examples are expected refused.
    const rel = relative(root, p);
    add("repo:" + rel, /\/(illegal|nocompile)\//.test(rel) ? "refuse" : "accept", "main",
      readFileSync(p, "latin1"));
  }
  writeFileSync(join(cache, "manifest.tsv"), rows.join("\n") + "\n");
  console.log(`parse-corpus: ${rows.length} units written to ${relative(root, cache)}/manifest.tsv`);
} else if (mode === "report") {
  // Why a test's verdict differs from solc's expectation. `A`: accepted
  // here, refused by solc's parser; `R`: refused here, accepted by solc's
  // parser. A rule applies only in its direction and, where it can, to the
  // message this parser gave.
  const YUL = ["5568", "6272", "7104"];
  const some = (t, f) => t.codes.length > 0 && t.codes.every(f);
  const msg = (t) => t.msgs.join(" | ");
  const rules = [
    ["A", (id, t) => /^repo:.*\/(illegal|nocompile)\//.test(id),
      "repository negative example: refused by solc's later stages, not its parser"],
    ["A", (id, t) => some(t, (c) => ["1684", "5333", "6281"].includes(c)),
      "pragma: version and pragma words are S01's settings check; S00 keeps the words"],
    ["A", (id, t) => some(t, (c) => ["1114", "3716"].includes(c)),
      "SPDX license comment: trivia here, checked by solc's parser"],
    ["A", (id, t) => some(t, (c) => YUL.includes(c)),
      "Yul analysis (builtin and reserved names): assembly is outside the profile (parseInProfile)"],
    ["A", (id, t) => some(t, (c) => c === "7319"), "solc's nesting-depth limit"],
    ["R", (id, t) => /outside a loop|nested unchecked|empty struct/.test(msg(t)),
      "solc's syntax checker, a later stage: intrinsic in S00 (SCtx) or the grammar"],
    ["R", (id, t) => /underscores/.test(id) && /malformed number/.test(msg(t)),
      "misplaced `_` in a number: solc's syntax checker, refused by the lexer"],
    ["R", (id, t) => /Syn\.prec/.test(msg(t)) && /ternary|OperatorBoundaries/.test(id),
      "grammar/solc disagreement refused by Syn.prec"],
    ["R", (id, t) => /fallback|receive/.test(id),
      "fallback/receive form without an S00 tree (solc refuses it later)"],
    ["R", (id, t) => /^solc:constructor\/|function_type_constructor/.test(id),
      "constructor attributes without an S00 tree (solc refuses them later)"],
    ["R", (id, t) => /^solc:abstract\/|unimplemented_library|inheriting_library/.test(id) &&
      /expected 'contract'|expected '\{'/.test(msg(t)),
      "abstract interface/library or library inheritance: no S00 tree (grammar refuses)"],
    ["R", (id, t) => /mutability|constant_input_parameter|location_specifiers|as_function_param|cannot_be_constant/.test(id) &&
      /expected '\)'|expected an identifier/.test(msg(t)),
      "parameter attribute other than a data location: grammar refuses (solc later)"],
    ["R", (id, t) => /^solc:userDefinedValueType\//.test(id) && /elementary type/.test(msg(t)),
      "UDVT over a non-elementary type: grammar refuses (solc later)"],
    ["R", (id, t) => /metaTypes|max_keyword/.test(id) && /type name|expected '\)'/.test(msg(t)),
      "`type(…)` of an expression: S00's metaType takes a type name"],
    ["R", (id, t) => /empty_array_literal/.test(id) && /expected an expression/.test(msg(t)),
      "`[]`: grammar refuses (solc later)"],
    ["R", (id, t) => /^solc:constants\/|constant_forward_reference_struct|attached_free_function/.test(id) &&
      /expected '='|expected 'constant'/.test(msg(t)),
      "file-level constant without value or non-constant: S00's constant needs `constant … = e`"],
    ["R", (id, t) => /^solc:tryCatch\//.test(id) && /empty catch parameters/.test(msg(t)),
      "`catch Name()` with no parameters: no S00 tree"],
    ["R", (id, t) => /^solc:inlineAssembly\//.test(id) && /Syn\.prec/.test(msg(t)),
      "Yul multi-variable assignment from a non-call: grammar refuses (solc later)"],
    ["R", (id, t) => /^solc:inlineAssembly\//.test(id) && /Yul|expected '\('|expected '\)'/.test(msg(t)),
      "Yul dotted names in declarations: grammar refuses (solc later)"],
  ];
  const reason = (id, t) =>
    (rules.find(([d, f]) => (d === "A") === t.accepted && f(id, t)) ?? [null, null, "unclassified"])[2];
  const manifest = readFileSync(join(cache, "manifest.tsv"), "utf8").trim().split("\n")
    .map((l) => l.split("\t"));
  const results = new Map(readFileSync(join(cache, "results.tsv"), "utf8").trim().split("\n")
    .map((l) => l.split("\t")).map(([file, verdict, roundtrip, msg]) => [file, { verdict, roundtrip, msg }]));
  const tests = new Map();
  for (const [expect, id, name, file, codes = ""] of manifest) {
    const r = results.get(file);
    if (!r) { console.error(`missing result for ${file}`); process.exit(2); }
    const t = tests.get(id) ?? { expect, accepted: true, roundtrip: true, msgs: [],
      codes: codes ? codes.split(",") : [] };
    if (r.verdict !== "ok") { t.accepted = false; t.msgs.push(`${name}: ${r.msg}`); }
    if (r.verdict === "ok" && r.roundtrip !== "same") t.roundtrip = false;
    tests.set(id, t);
  }
  const count = { solc: { accept: [0, 0], refuse: [0, 0] }, repo: { accept: [0, 0], refuse: [0, 0] } };
  const disagree = [];
  const reasons = {};
  let rtFail = [];
  for (const [id, t] of [...tests].sort()) {
    const src = id.startsWith("solc:") ? "solc" : "repo";
    const cell = count[src][t.expect];
    if (t.accepted) cell[0]++; else cell[1]++;
    const agrees = (t.expect === "accept") === t.accepted;
    if (!agrees) {
      const why = reason(id, t);
      reasons[why] = (reasons[why] ?? 0) + 1;
      disagree.push(`${id}\texpected ${t.expect}\t${t.accepted ? "accepted" : t.msgs.join(" | ")}\t${why}`);
    }
    if (t.accepted && !t.roundtrip) rtFail.push(id);
  }
  const summary = {
    note: "accepted/refused per expectation; see docs/feature-work/frontend-parse.md",
    solcExpectAccept: { accepted: count.solc.accept[0], refused: count.solc.accept[1] },
    solcExpectRefuse: { accepted: count.solc.refuse[0], refused: count.solc.refuse[1] },
    repo: { accepted: count.repo.accept[0], refused: count.repo.accept[1] },
    repoExpectRefuse: { accepted: count.repo.refuse[0], refused: count.repo.refuse[1] },
    disagreementReasons: reasons,
    roundtripFailures: rtFail,
    disagreements: disagree,
  };
  console.log(`solc syntax tests expected accepted: ${count.solc.accept[0]} accepted, ${count.solc.accept[1]} refused`);
  console.log(`solc syntax tests expected refused:  ${count.solc.refuse[0]} accepted, ${count.solc.refuse[1]} refused`);
  console.log(`repository .sol files:               ${count.repo.accept[0]} accepted, ${count.repo.accept[1]} refused`);
  console.log(`repository negative examples:        ${count.repo.refuse[0]} accepted, ${count.repo.refuse[1]} refused`);
  for (const [k, v] of Object.entries(reasons).sort((a, b) => b[1] - a[1])) console.log(`  ${v}\t${k}`);
  console.log(`round trip (print, parse again): ${rtFail.length} failures; ${disagree.length} disagreements`);
  if (process.argv.includes("--write")) {
    mkdirSync(dirname(baselinePath), { recursive: true });
    writeFileSync(baselinePath, JSON.stringify(summary, null, 1) + "\n");
    console.log(`wrote ${relative(root, baselinePath)}`);
  } else if (existsSync(baselinePath)) {
    const base = JSON.parse(readFileSync(baselinePath, "utf8"));
    const same = JSON.stringify(base) === JSON.stringify(summary) && !reasons.unclassified;
    console.log(same ? "baseline: unchanged" : "baseline: CHANGED");
    process.exit(same ? 0 : 1);
  }
} else {
  console.error("usage: node scripts/parse-corpus.mjs prepare | report [--write]");
  process.exit(2);
}
