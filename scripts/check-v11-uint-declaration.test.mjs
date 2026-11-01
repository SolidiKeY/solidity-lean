import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { pins, compare, STANDARD } from "./check-axiom-pins.mjs";

// Evidence-admission tests only. Actual execution and observations are established
// by the kernel-checked Lean laws/controls, not by this source-text test.
const cases = [
  ["SourceUintDefault", ["source_uint_default_run", "source_uint_default_intrinsic", "source_uint_default_memOK", "SourceUintMemoryAt.default_frame", "source_uint_default_word", "source_uint_default_lowfuel"]],
  ["SourceUintDeclaration", ["SourceUintMemoryAt.withLocals", "SourceUintMemoryAt.declaration_frame", "source_uint_declaration_word", "source_uint_declaration_timeouts"]],
  ["SourceUintDeclarationControls", ["populated_declaration", "populated_timeouts", "fresh_context_negative", "source_object_table", "nonuniform_run", "fresh_empty_observations"]],
];
function audit(text, module, expected) {
  const file = `Solidity/Backend/MemoryOps/${module}.lean`;
  const prefix = `Solidity.Backend.MemoryOps.${module.endsWith("Controls") ? module + "." : ""}`;
  const found = pins(text);
  assert.deepEqual(found.map(p => p.target).sort(), [...expected].sort());
  const records = Object.fromEntries(expected.map(n => [`${file}:${prefix}${n}`, [...(n === "fresh_context_negative" ? ["propext", "Quot.sound"] : STANDARD)].sort()]));
  const actual = new Map(found.map(p => [`${file}:${p.name}`, { ...p, file }]));
  const result = compare(actual, records);
  assert.deepEqual(result.errors, []);
  assert.deepEqual(result.notes, []);
}
for (const [module, expected] of cases) {
  const text = readFileSync(`Solidity/Backend/MemoryOps/${module}.lean`, "utf8");
  test(`${module}: all headline laws/controls have exact published standard pins`, () => audit(text, module, expected));
  test(`${module}: dropping a headline guard is rejected`, () => {
    const bad = text.replace(`#guard_msgs (whitespace := lax) in #print axioms ${expected[0]}` + String.fromCharCode(10), "");
    assert.ok(bad !== text, "mutation must apply");
    assert.throws(() => audit(bad, module, expected));
  });
  test(`${module}: unsafe axiom mutation is rejected`, () => {
    const bad = text.replace("depends on axioms: [propext, Classical.choice, Quot.sound]",
      "depends on axioms: [propext, Classical.choice, Quot.sound, sorryAx]");
    assert.ok(bad !== text, "mutation must apply");
    assert.throws(() => audit(bad, module, expected));
  });
  test(`${module}: renamed print target is rejected`, () => {
    const bad = text.replace(`#print axioms ${expected[0]}`, `#print axioms ${expected[1]}`);
    assert.ok(bad !== text, "mutation must apply");
    assert.throws(() => audit(bad, module, expected));
  });
}
