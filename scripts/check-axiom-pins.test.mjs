import { test } from "node:test";
import assert from "node:assert/strict";
import { pins, compare } from "./check-axiom-pins.mjs";

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
