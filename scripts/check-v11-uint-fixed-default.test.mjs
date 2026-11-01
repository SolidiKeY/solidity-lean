import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { pins, compare, STANDARD } from "./check-axiom-pins.mjs";

// Evidence-admission tests only. Actual execution and observations are established
// by the kernel-checked Lean laws/controls, not by this source-text test.
const cases = [
  ["SourceUintFixedDefault", ["source_uint_zeroElems_run", "source_uint_fixed_zeroData", "source_uint_fixed_zeroVal", "sourceUintFixedObject_zero", "source_uint_fixed_intrinsic", "source_uint_zeroElems_timeout", "source_uint_fixed_zeroData_timeout", "source_uint_fixed_zeroVal_timeout", "SourceUintFixedAt.read", "SourceUintFixedAt.bounds", "sourceUintFixedObject_wk", "SourceUintFixedAt.keeps", "source_uint_fixed_memOK", "source_uint_fixed_declaration", "source_uint_fixed_old_frame", "source_uint_fixed_word", "SourceUintFixedAt.eval_index"]],
  ["SourceUintFixedDeclaration", ["source_uint_fixed_alloc_memOK", "source_uint_fixed_declaration_word", "source_uint_fixed_declaration_timeout"]],
  ["SourceUintFixedDefaultControls", ["initial_views", "populated_declaration", "positive_examples", "element_boundary", "insufficient_horizons", "wrong_type_length_identity", "zero_padding_kernel_only", "raw_space_wrap"]]
];
function audit(text, module, expected) {
  const file = `Solidity/Backend/MemoryOps/${module}.lean`;
  const prefix = `Solidity.Backend.MemoryOps.${module.endsWith("Controls") ? module + "." : ""}`;
  const found = pins(text);
  assert.deepEqual(found.map(p => p.target).sort(), [...expected].sort());
  const records = Object.fromEntries(expected.map(n => [`${file}:${prefix}${n}`, [...(["sourceUintFixedObject_zero", "sourceUintFixedObject_wk"].includes(n) ? ["propext", "Quot.sound"] : STANDARD)].sort()]));
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
    const bad = text.replace(`#print axioms ${expected[0]}`, `#print axioms ${expected[1] ?? "missing_target"}`);
    assert.ok(bad !== text, "mutation must apply");
    assert.throws(() => audit(bad, module, expected));
  });
}
