import { test } from "node:test";
import assert from "node:assert/strict";
import { pins, compare, collect } from "./check-axiom-pins.mjs";

test("pins are read from guarded #print axioms, primes and wrapping included", () => {
  assert.deepEqual(pins("/-- info: 'A.b'' depends on axioms: [propext,\n Quot.sound] -/\n#guard_msgs in #print axioms b'\n"),
    [{ name: "A.b'", target: "b'", axioms: ["Quot.sound", "propext"] }]);
  assert.deepEqual(pins("/-- info: 'A.c' does not depend on any axioms -/\n#guard_msgs (whitespace := lax) in\n#print axioms A.c"),
    [{ name: "A.c", target: "A.c", axioms: [] }]);
  assert.deepEqual(pins("#print axioms A.d"), []);
  assert.deepEqual(pins("/- /-- info: 'A.e' depends on axioms: [sorryAx] -/\n#guard_msgs in #print axioms A.e -/"), []);
});

test("only the adjacent doc comment counts", () => {
  const p = pins("/-- info: 'A.x' depends on axioms: [propext] -/\ndef y := 1\n/-- other -/\n#guard_msgs in #print axioms A.z\n");
  assert.deepEqual(p, [{ name: "A.z", target: "A.z", axioms: null }]);
});

test("sorryAx, growth, renaming and lost pins fail; shrinking and new pins are notes", () => {
  const f = (o) => new Map(Object.entries(o).map(([n, a]) => [`F.lean:${n}`, { name: n, target: n, axioms: a, file: "F.lean" }]));
  assert.equal(compare(f({ x: ["sorryAx"] }), { "F.lean:x": ["sorryAx"] }).errors.length, 1);
  assert.equal(compare(f({ x: ["Quot.sound", "propext"] }), { "F.lean:x": ["propext"] }).errors.length, 1);
  assert.equal(compare(f({}), { "F.lean:x": [] }).errors.length, 1);
  assert.deepEqual(compare(f({ x: [] }), { "F.lean:x": ["propext"] }).errors, []);
  assert.equal(compare(f({ x: [] }), { "F.lean:x": ["propext"] }).notes.length, 1);
  assert.equal(compare(f({ y: [] }), {}).notes.length, 1);
  const g = new Map([["F.lean:A.b", { name: "A.b", target: "c", axioms: [], file: "F.lean" }]]);
  assert.equal(compare(g, { "F.lean:A.b": [] }).errors.length, 1);
});

// The inventory follows project sources, not local dependency/build caches.
test("collect includes all source areas and excludes nested Lake caches", async () => {
  const { mkdtempSync, mkdirSync, writeFileSync, rmSync } = await import("node:fs");
  const { join, dirname } = await import("node:path");
  const { tmpdir } = await import("node:os");
  const root = mkdtempSync(join(tmpdir(), "axiom-collect-"));
  const files = ["Solidity/Keep.lean", "Bridge/SolidityBridge/Keep.lean",
    "tests/Keep.lean", "Bridge/.lake/packages/mathlib/MathlibTest/Ignore.lean",
    "Solidity/Nested/.lake/build/Ignore.lean"];
  try {
    for (const file of files) {
      mkdirSync(dirname(join(root, file)), { recursive: true });
      writeFileSync(join(root, file), "/-- info: 'pin' does not depend on any axioms -/\n#guard_msgs in #print axioms pin\n");
    }
    assert.deepEqual([...collect(root).keys()].sort(),
      files.slice(0, 3).map(file => file + ":pin").sort());
  } finally { rmSync(root, { recursive: true, force: true }); }
});

import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync, symlinkSync } from "node:fs";
import { join, dirname } from "node:path";
import { tmpdir } from "node:os";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { FRAGMENTS, CANONICAL_FRAGMENTS, parseUnique, pinSource, validatePinObject,
  legacyPaths, fragmentPath, validateFragments, groupFragments, planFragments,
  writeFragments, compactInventory, readFragmentFiles } from "./check-axiom-pins.mjs";
const legacy = `${FRAGMENTS}/Solidity/F.json`, key = "Solidity/F.lean:x";
const raw = ` { ${JSON.stringify(key)} : [ ] }\n`;
function fixture(run) {
  const root = mkdtempSync(join(tmpdir(), "axiom-storage-"));
  const put = (file, value) => { mkdirSync(dirname(join(root, file)), { recursive: true }); writeFileSync(join(root, file), value); };
  const git = (...args) => execFileSync("git", args, { cwd: root, encoding: "utf8" });
  try {
    git("init", "-q"); git("config", "user.email", "fixture@example.invalid"); git("config", "user.name", "fixture");
    put(legacy, raw); git("add", "."); git("commit", "-qm", "immutable seed");
    put("scripts/hygiene/allow.json", JSON.stringify({seed: git("rev-parse", "HEAD").trim()}));
    run(root, put, git);
  } finally { rmSync(root, { recursive: true, force: true }); }
}

test("immutable seed, not existing files, chooses legacy eligibility; full UTF8 source hashes", () => fixture((root, put) => {
  const eligible = legacyPaths(root), source = "Solidity/Δ/é.lean";
  put(`${FRAGMENTS}/Solidity/New.json`, "{}\n");
  assert.equal(fragmentPath("Solidity/F.lean", eligible), legacy);
  assert.equal(fragmentPath(source, eligible), `${CANONICAL_FRAGMENTS}/${createHash("sha256").update(Buffer.from(source, "utf8")).digest("hex")}.json`);
  assert.match(fragmentPath("Solidity/New.lean", eligible), /^scripts\/axiom-pins\/[0-9a-f]{64}\.json$/u);
  assert.throws(() => writeFragments(root, {[key]: []}), /unrecognized empty fragment/u);
  assert.equal(readFileSync(join(root, legacy), "utf8"), raw);
}));

test("mixed union, compact ordering, repeat generation and legacy bytes are stable", () => fixture(root => {
  const eligible = legacyPaths(root), map = {[key]: [], "Solidity/Δ/é.lean:z": ["propext"], "Solidity/Δ/é.lean:a": []};
  writeFragments(root, map);
  const files = readFragmentFiles(root), check = validateFragments(files, eligible);
  assert.deepEqual(check.merged, map);
  assert.equal(files[legacy], raw);
  assert.equal(Object.keys(files).length, 2);
  const compact = compactInventory(map);
  assert.equal(compact, JSON.stringify(Object.fromEntries(Object.entries(map).sort(([a], [b]) => a.localeCompare(b)))) + "\n");
  assert.deepEqual(JSON.parse(compact), map);
  writeFragments(root, Object.fromEntries(Object.entries(map).reverse()));
  assert.deepEqual(readFragmentFiles(root), files);
  assert.deepEqual(planFragments(files, map, eligible), {writes: {}, deletes: []});
}));

test("duplicate keys including escaped equivalents and duplicate roots are rejected", () => {
  assert.throws(() => parseUnique('{"x":[],"\\u0078":[]}'), /duplicate key/u);
  assert.throws(() => parseUnique('{"nested":{"x":1,"x":2}}'), /duplicate key/u);
  assert.deepEqual(parseUnique('{"x":["a", "a"], "nested":{"x":1}}'), {x:["a","a"],nested:{x:1}});
  const eligible = new Set([legacy]);
  assert.throws(() => validateFragments({[legacy]:raw, [fragmentPath("Solidity/F.lean", new Set())]:raw}, eligible), /duplicate across fragments/u);
});

test("malformed/mixed sources, invalid lists, nonstandard axioms and collisions fail", () => {
  const eligible = new Set([legacy]);
  for (const k of ["missing", "../F.lean:x", "/F.lean:x", "Solidity/../F.lean:x", "F.lean:"])
    assert.throws(() => pinSource(k), /malformed/u);
  assert.equal(pinSource("Solidity/F:Δ.lean:a:b"), "Solidity/F:Δ.lean");
  for (const value of [null, {}, 3, ["sorryAx"], ["newAxiom"], [1]])
    assert.throws(() => validatePinObject({[key]:value}), /axiom/u);
  for (const value of [null, [], "x"]) assert.throws(() => validatePinObject(value), /not an object/u);
  assert.throws(() => validateFragments({[legacy]:JSON.stringify({[key]:[], "Solidity/G.lean:y":[]})}, eligible), /mixed source/u);
  assert.throws(() => validateFragments({[`${CANONICAL_FRAGMENTS}/${"0".repeat(64)}.json`]:raw}, eligible), /wrong fragment/u);
  assert.throws(() => groupFragments({"A.lean:x":[],"B.lean:y":[]}, new Set(), () => "0".repeat(64)), /collision/u);
});

test("preflight rejects malformed/unrecognized/symbolic files without pruning or writes", () => fixture((root, put) => {
  for (const [bad, text] of [[`${CANONICAL_FRAGMENTS}/unknown.json`,"{"], [`${FRAGMENTS}/unexpected.txt`,"text"]]) {
    put(bad,text);
    assert.throws(() => writeFragments(root, {"Solidity/New.lean:x": []}));
    assert.equal(readFileSync(join(root, legacy), "utf8"),raw);
    assert.equal(readFileSync(join(root,bad),"utf8"),text);
    rmSync(join(root,bad));
  }
  const link = `${CANONICAL_FRAGMENTS}/link.json`;
  mkdirSync(dirname(join(root, link)),{recursive:true}); symlinkSync(join(root,legacy),join(root,link));
  assert.throws(() => writeFragments(root, {}), /symbolic/u);
  assert.equal(readFileSync(join(root,legacy),"utf8"),raw);
}));

test("verified stale paths alone are pruned and missing guards retain compare errors/notes", () => fixture(root => {
  const current = {[key]:[]}, found = new Map([[key,{name:"x",target:"x",file:"Solidity/F.lean",axioms:[]}]]);
  assert.equal(compare(found,{}).notes.length,1);
  assert.equal(compare(new Map(),current).errors.length,1);
  writeFragments(root,current);
  assert.equal(compare(found,validateFragments(readFragmentFiles(root),legacyPaths(root)).merged).notes.length,0);
  writeFragments(root,{});
  assert.deepEqual(readFragmentFiles(root),{});
  assert.equal(compare(found,{}).notes.length,1);
}));


test("historical seed tree before allow.json remains eligible; malformed historical policy fails", () => fixture((root, put, git) => {
  const seed = git("rev-parse", "HEAD").trim(), good = readFileSync(join(root,"scripts/hygiene/allow.json"),"utf8");
  assert.ok(legacyPaths(root,seed).has(legacy));
  put("scripts/hygiene/allow.json","{"); git("add","."); git("commit","-qm","malformed historical policy");
  const bad = git("rev-parse","HEAD").trim();
  put("scripts/hygiene/allow.json",good);
  assert.throws(() => legacyPaths(root,bad));
}));

test("writer rejects symbolic ancestors without touching the external target", () => {
  const root=mkdtempSync(join(tmpdir(),"axiom-parent-")), outside=mkdtempSync(join(tmpdir(),"axiom-outside-"));
  try {
    mkdirSync(join(outside,"g07-axiom-pins.d"));
    const file=join(outside,"g07-axiom-pins.d","keep.txt"); writeFileSync(file,"keep");
    symlinkSync(outside,join(root,"scripts"));
    assert.throws(() => writeFragments(root,{}),/symbolic/u);
    assert.equal(readFileSync(file,"utf8"),"keep");
  } finally { rmSync(root,{recursive:true,force:true}); rmSync(outside,{recursive:true,force:true}); }
});
