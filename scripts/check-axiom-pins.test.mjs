import { test } from "node:test";
import assert from "node:assert/strict";
import { pins, compare } from "./check-axiom-pins.mjs";

test("pins are read from guarded #print axioms, primes and wrapping included", () => {
  assert.deepEqual(pins("/-- info: 'A.b'' depends on axioms: [propext,\n Quot.sound] -/\n#guard_msgs in #print axioms b'\n"),
    [{ name: "A.b'", axioms: ["Quot.sound", "propext"] }]);
  assert.deepEqual(pins("/-- info: 'A.c' does not depend on any axioms -/\n#guard_msgs in\n#print axioms A.c"),
    [{ name: "A.c", axioms: [] }]);
  assert.deepEqual(pins("#print axioms A.d"), []);
});

test("sorryAx, growth and lost pins fail; shrinking and new pins are notes", () => {
  const f = (o) => new Map(Object.entries(o).map(([n, a]) => [n, { axioms: a, file: "F.lean" }]));
  assert.equal(compare(f({ x: ["sorryAx"] }), { x: ["sorryAx"] }).errors.length, 1);
  assert.equal(compare(f({ x: ["Quot.sound", "propext"] }), { x: ["propext"] }).errors.length, 1);
  assert.equal(compare(f({}), { x: [] }).errors.length, 1);
  assert.deepEqual(compare(f({ x: [] }), { x: ["propext"] }).errors, []);
  assert.equal(compare(f({ x: [] }), { x: ["propext"] }).notes.length, 1);
  assert.equal(compare(f({ y: [] }), {}).notes.length, 1);
});
