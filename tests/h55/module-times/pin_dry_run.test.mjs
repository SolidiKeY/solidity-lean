// Guard regression: dry-run inventory collapses duplicate pin occurrences.
import test from "node:test";
import assert from "node:assert/strict";
import { inventory } from "../../../scripts/h55/module-times/pin_dry_run.mjs";

test("preserves raw occurrences and unresolved destinations", () => {
  const guard = "/-- info: 'N.x' does not depend on any axioms -/\n#guard_msgs in #print axioms N.x\n";
  const result = inventory([{file:"Solidity/Foo/A.lean", text:guard + guard}]);
  assert.equal(result.occurrences, 2);
  assert.deepEqual(result.duplicate_checker_keys, [["Solidity/Foo/A.lean:N.x", 2]]);
  assert.equal(result.areas["Solidity/Foo"].files, 1);
  assert.deepEqual(result.duplicate_suggested_keys, [["Solidity/Foo/AxiomPins.lean:N.x", 2]]);
  assert.ok(result.rows.every(x => x.suggested_destination === "Solidity/Foo/AxiomPins.lean"));
  assert.deepEqual(result.rows.map(x => x.axioms), [[], []]);
  assert.deepEqual(result.rows.map(x => x.observed_block), [guard.trimEnd(), guard.trimEnd()]);
  assert.equal(result.rows[0].start_byte, 0);
  assert.equal(result.rows[1].start_byte, Buffer.byteLength(guard));
  assert.ok(result.rows.every(x => x.destination === null && x.relocation === "unresolved"));
});

test("reports UTF-8 byte spans over observed source", () => {
  const text = "-- λ 前\n/-- info: 'N.x' does not depend on any axioms -/\n#guard_msgs in #print axioms N.x\n";
  const [row] = inventory([{ file:"Solidity/Foo/A.lean", text }]).rows;
  assert.equal(Buffer.from(text).subarray(row.start_byte, row.end_byte).toString("utf8"), row.observed_block);
  assert.equal(row.start_byte, Buffer.byteLength("-- λ 前\n"));
});
