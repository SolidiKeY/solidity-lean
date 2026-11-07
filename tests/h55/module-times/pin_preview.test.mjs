// Guard regression: a preview silently drops guards or mutates the source.
import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync, symlinkSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { inventory } from "../../../scripts/h55/module-times/pin_dry_run.mjs";
import { preview } from "../../../scripts/h55/module-times/pin_preview.mjs";

test("copies guards to a preview and refuses drift or occupied destinations", () => {
  const root = mkdtempSync(join(tmpdir(), "h109-preview-"));
  try {
    const file = "Solidity/Foo/A.lean", full = join(root, file);
    mkdirSync(join(root, "Solidity/Foo"), {recursive:true});
    const text = "namespace N\n/-- info: 'N.x' does not depend on any axioms -/\n#guard_msgs in #print axioms N.x\nend N\n";
    writeFileSync(full, text);
    const report = inventory([{file, text}]);
    const [row] = preview(root, report, [file]);
    assert.equal(readFileSync(full, "utf8"), text);
    assert.ok(row.preview_pin_module.includes(report.rows[0].observed_block));
    assert.ok(!row.preview_source.includes("#guard_msgs"));
    assert.equal(row.relocation, "unresolved-not-applied");
    writeFileSync(join(root, "Solidity/Foo/AxiomPins.lean"), "occupied");
    assert.throws(() => preview(root, report, [file]), /area not empty/);
    rmSync(join(root, "Solidity/Foo/AxiomPins.lean"));
    symlinkSync("missing", join(root, "Solidity/Foo/AxiomPins.lean"));
    assert.throws(() => preview(root, report, [file]), /area not empty/);
    rmSync(join(root, "Solidity/Foo/AxiomPins.lean"));
    writeFileSync(full, text + "-- changed\n");
    assert.throws(() => preview(root, report, [file]), /differs/);
  } finally { rmSync(root, {recursive:true, force:true}); }
});
