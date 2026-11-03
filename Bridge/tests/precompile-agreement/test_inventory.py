"""Mutation controls for the source inventory gate, not EVM tests."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("checker", ROOT / "scripts/check-precompile-agreement.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class InventoryControls(unittest.TestCase):
    def setUp(self):
        self.data = json.loads(checker.INVENTORY.read_text())

    def test_complete_source_inventory(self):
        self.assertEqual(checker.validate(self.data), [])

    def test_each_address_omission_rejected(self):
        for i in range(18):
            data = copy.deepcopy(self.data)
            del data["rows"][i]
            self.assertTrue(checker.validate(data), i)

    def test_duplicate_rejected(self):
        self.data["rows"][-1] = self.data["rows"][0]
        self.assertTrue(checker.validate(self.data))

    def test_address_change_rejected(self):
        self.data["rows"][-1]["address"] = 18
        self.assertTrue(checker.validate(self.data))

    def test_hash_change_rejected(self):
        self.data["pins"]["Bridge/vendor/EvmYul/EVM/PrecompiledContracts.lean"] = "0" * 64
        self.assertTrue(checker.validate(self.data))

    def test_missing_pin_rejected(self):
        del self.data["pins"]["Bridge/vendor/EvmYul/EVM/PrecompiledContracts.lean"]
        self.assertTrue(checker.validate(self.data))

    def test_invented_proof_rejected(self):
        self.data["rows"][3]["proof_status"] = "proved"
        self.data["rows"][3]["proofs"] = ["fake"]
        self.assertTrue(checker.validate(self.data))

    def test_swapped_vendor_definition_rejected(self):
        self.data["rows"][3]["vendor_definition"] = "Ξ_SHA256"
        self.assertTrue(checker.validate(self.data))

    def test_wrong_core_module_rejected(self):
        for replacement in ("does-not-exist.lean", "Solidity/Precompiles/Modexp.lean"):
            self.data["rows"][3]["core_module"] = replacement
            self.assertTrue(checker.validate(self.data))

    def test_missing_vendor_closure_pin_rejected(self):
        del self.data["pins"]["Bridge/vendor/EvmYul/PerformIO.lean"]
        self.assertTrue(checker.validate(self.data))

    def test_changed_classification_rejected(self):
        self.data["rows"][3]["classification"] = "fork-mismatch"
        self.assertTrue(checker.validate(self.data))

    def test_hidden_unsupported_row_rejected(self):
        self.data["rows"][10]["classification"] = "identity-candidate"
        self.assertTrue(checker.validate(self.data))


if __name__ == "__main__":
    unittest.main()
