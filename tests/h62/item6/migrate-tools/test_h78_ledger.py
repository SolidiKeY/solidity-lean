#!/usr/bin/env python3
import copy, importlib.util, sys, unittest
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location("h78", ROOT / "scripts/h62/item6/migrate-tools/h78-ledger.py")
h78 = importlib.util.module_from_spec(spec); spec.loader.exec_module(h78)

class H78Controls(unittest.TestCase):
    def snapshot(self):
        return {"base": "old", "kernel_declaration_count": 3, "modules": [{"module": "M", "declarations": [
            {"name": n, "level_params": ["u"], "type_expr": "forallE binder Type body implicit", "interface_repr_sha256": "hash", "is_theorem": False, "is_unsafe": False}
            for n in ["M.noConfusion", "M.recOn", "_private.M.match_1"]]}]}
    def test_no_generated_or_private_exclusion(self):
        data = h78.build(self.snapshot(), "new")
        self.assertEqual({r["name"] for r in data["declarations"]}, {"M.noConfusion", "M.recOn", "_private.M.match_1"})
    def test_visibility_and_kind_are_not_guessed(self):
        for row in h78.build(self.snapshot(), "new")["declarations"]:
            self.assertIsNone(row["old_visibility"]); self.assertIsNone(row["old_kind"])
    def test_incomplete_snapshot_rejected(self):
        data = self.snapshot(); data["modules"][0]["declarations"].pop()
        with self.assertRaisesRegex(ValueError, "coverage"): h78.build(data, "new")
    def test_duplicate_rejected(self):
        data = self.snapshot(); data["modules"][0]["declarations"][1] = copy.deepcopy(data["modules"][0]["declarations"][0])
        with self.assertRaisesRegex(ValueError, "duplicate"): h78.build(data, "new")
    def test_actual_shim_requires_all_signatures(self):
        data = h78.build(self.snapshot(), "new"); data["implemented_shims"] = [{"name": "M.noConfusion", "old_signature": "old", "new_signature": "new"}]
        with self.assertRaisesRegex(ValueError, "shim_signature"): h78.validate(data)
    def test_cannot_claim_compatibility_from_old_only_data(self):
        data = h78.build(self.snapshot(), "new"); data["compatibility_established"] = True
        with self.assertRaisesRegex(ValueError, "cannot establish"): h78.validate(data)

if __name__ == "__main__": unittest.main()
