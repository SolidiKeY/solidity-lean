#!/usr/bin/env python3
"""Negative controls against incomplete/misclassified frozen-interface evidence."""
import copy, importlib.util, sys, unittest
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location("api_inventory", ROOT / "scripts/h62/item6/migrate-tools/normalize-api.py")
api = importlib.util.module_from_spec(spec); spec.loader.exec_module(api)

class InventoryControls(unittest.TestCase):
    def setUp(self):
        self.census = {"base": "test", "modules": [{"module": "Fixture", "path": "Fixture.lean", "sha256": "0"*64, "declaration_candidates": [{"kind": "theorem", "source_head": "proof : True"}]}]}
        self.records = [{"module": "Fixture", "declarations": [{"name": "Fixture.proof", "type_expr": "True", "level_params": [], "is_unsafe": False, "is_theorem": True}], "source_theorems": ["Fixture.proof"], "source_theorem_axiom_union": [], "module_theorems": ["Fixture.proof"], "module_theorem_axiom_union": []}]
    def test_missing_module_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "module set"): api.normalize([], self.census)
    def test_duplicate_module_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "duplicate module"): api.normalize(self.records*2, self.census)
    def test_missing_theorem_is_rejected(self):
        self.records[0]["source_theorems"] = []
        with self.assertRaisesRegex(ValueError, "theorem coverage"): api.normalize(self.records, self.census)
    def test_missing_generated_theorem_audit_is_rejected(self):
        self.records[0]["module_theorems"] = []
        with self.assertRaisesRegex(ValueError, "kernel theorem coverage"): api.normalize(self.records, self.census)
    def test_unrelated_passing_receipt_is_rejected(self):
        receipt = {"passed": True, "status": "complete", "modules": [{"module": "Unrelated"}]}
        with self.assertRaisesRegex(ValueError, "inventory module"): api.validate_receipt(receipt, Path("log"), Path("generator"))
    def test_wrong_log_is_rejected(self):
        receipt = {"passed": True, "status": "complete", "modules": [{"module": "tests.h62.item6.migrate-tools.ApiInventory", "exit": 0, "blocker": None, "log": "/wrong/log", "command": ["lean", "/generator"]}]}
        with self.assertRaisesRegex(ValueError, "receipt/log"): api.validate_receipt(receipt, Path("/actual/log"), Path("/generator"))
    def test_type_change_changes_frozen_hash(self):
        changed = copy.deepcopy(self.records); changed[0]["declarations"][0]["type_expr"] = "False"
        before = api.normalize(self.records, self.census)["modules"][0]["interface_repr_sha256"]
        after = api.normalize(changed, self.census)["modules"][0]["interface_repr_sha256"]
        self.assertNotEqual(before, after)

if __name__ == "__main__": unittest.main()
