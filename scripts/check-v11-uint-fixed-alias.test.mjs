import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { pins, compare, STANDARD } from "./check-axiom-pins.mjs";

// Evidence-admission tests only. Actual execution and observations are established
// by the kernel-checked Lean laws/controls, not by this source-text test.
const cases = [
  [
    "SourceUintFixedAlias",
    [
      "source_locals_get_set_other",
      "fixed_alias_scalar_frames",
      "source_uint_fixed_alias_word"
    ]
  ],
  [
    "SourceUintFixedAliasProgram",
    [
      "source_uint_fixed_alias_program_word"
    ]
  ],
  [
    "SourceUintFixedAliasFailure",
    [
      "source_uint_fixed_alias_reject"
    ]
  ],
  [
    "SourceUintFixedAliasControls",
    [
      "initial_views",
      "alias_cases",
      "reached_program",
      "word_vectors",
      "endpoint",
      "late_timeout",
      "stale_prefix",
      "selected_reads"
    ]
  ]
];

function audit(text, module, expected) {
  const file = `Solidity/Backend/MemoryOps/${module}.lean`;
  const prefix = `Solidity.Backend.MemoryOps.${module.endsWith("Controls") ? module + "." : ""}`;
  const found = pins(text);
  assert.deepEqual(found.map(p => p.target).sort(), [...expected].sort());
  const records = Object.fromEntries(expected.map(n => [`${file}:${prefix}${n}`, [...(n === "source_locals_get_set_other" ? [] : STANDARD)].sort()]));
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
