import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { pins, compare, STANDARD } from "./check-axiom-pins.mjs";

// Evidence-admission tests only. Actual execution and observations are established
// by the kernel-checked Lean laws/controls, not by this source-text test.
const cases = [
  [
    "SourceUintFixedCompoundSource",
    [
      "SourceUintFixedAt.compound_add",
      "SourceUintFixedAt.compound_add_overflow",
      "SourceUintFixedAt.compound_add_bounds",
      "source_uint_fixed_add_timeout"
    ]
  ],
  [
    "SourceUintFixedCompound",
    [
      "fixed_uint_add_certificate",
      "resolved_uint_fixed_add_word",
      "resolved_uint_fixed_add_overflow_word"
    ]
  ],
  [
    "SourceUintFixedCompoundSequence",
    [
      "resolved_uint_fixed_add_twice_word",
      "resolved_uint_fixed_add_late_overflow_word"
    ]
  ],
  [
    "SourceUintFixedCompoundBounds",
    [
      "resolved_uint_fixed_add_bounds_word"
    ]
  ],
  [
    "SourceUintFixedCompoundControls",
    [
      "initial_views",
      "alias_updates",
      "late_overflow",
      "bounds_timeout",
      "word_vectors",
      "declared_updates",
      "boundary_reads",
      "empty_kernel_only",
      "fresh_word_vectors",
      "zero_rhs"
    ]
  ],
  ["SourceUintFixedDeclareCompound", ["source_uint_fixed_declare_compound_word", "source_uint_fixed_declare_compound_timeout"]],
  ["SourceUintFixedDeclareCompoundOverflow", ["source_uint_fixed_declare_compound_overflow_word"]],
  ["SourceUintFixedDeclareCompoundControls", ["reached_program", "word_vectors", "late_overflow", "boundary33"]]

];

function audit(text, module, expected) {
  const file = `Solidity/Backend/MemoryOps/${module}.lean`;
  const prefix = `Solidity.Backend.MemoryOps.${module.endsWith("Controls") ? module + "." : ""}`;
  const found = pins(text);
  assert.deepEqual(found.map(p => p.target).sort(), [...expected].sort());
  const records = Object.fromEntries(expected.map(n => [`${file}:${prefix}${n}`, [...(STANDARD)].sort()]));
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
