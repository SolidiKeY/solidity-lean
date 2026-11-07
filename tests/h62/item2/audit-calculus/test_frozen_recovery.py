"""Refusal controls for lexical-only frozen snapshot recovery."""
import copy
import importlib.util
from pathlib import Path
import sys
import unittest

SCRIPTS = Path(__file__).resolve().parents[4] / "scripts/h62/item2/audit-calculus"
sys.path.insert(0, str(SCRIPTS))
import recover_frozen_census as recovery


class FrozenRecoveryControls(unittest.TestCase):
    def setUp(self):
        self.scope = {"base": recovery.BASE,
                      "module_maps": [{"path": "docs/module-map/calculus.md", "sha256": "map"}],
                      "mapped_sources": [{"path": "Solidity/A.lean", "sha256": "source"}],
                      "source_declarations": 1}
        self.census = {"sources": [{"path": "Solidity/A.lean", "sha256": "source"}],
                       "missing_module_paths": [], "declarations": [{}],
                       "counts": {"joint_witnesses_verified": 0}}

    def test_valid_lexical_control_does_not_count_proofs(self):
        recovery.validate_census(self.scope, self.census)
        self.assertEqual(self.census["counts"]["joint_witnesses_verified"], 0)

    def test_path_escape_and_noncanonical_spellings_refused(self):
        for path in ["/Solidity/A.lean", "Solidity/../A.lean", "Solidity//A.lean",
                     "Solidity/./A.lean", "outside/A.lean", "Solidity/A\\B.lean"]:
            with self.subTest(path=path), self.assertRaises(ValueError):
                recovery.safe_path(path)

    def test_duplicate_snapshot_source_refused(self):
        self.scope["mapped_sources"] *= 2
        with self.assertRaisesRegex(ValueError, "duplicate"):
            recovery.snapshot_entries(self.scope)

    def test_unexpected_base_refused(self):
        self.scope["base"] = "other"
        with self.assertRaisesRegex(ValueError, "base"):
            recovery.snapshot_entries(self.scope)

    def test_changed_or_missing_source_refused(self):
        for sources in [[], [{"path": "Solidity/A.lean", "sha256": "changed"}],
                        self.census["sources"] * 2]:
            altered = copy.deepcopy(self.census)
            altered["sources"] = sources
            with self.subTest(sources=sources), self.assertRaises(ValueError):
                recovery.validate_census(self.scope, altered)

    def test_missing_mapped_path_refused(self):
        self.census["missing_module_paths"] = [{"path": "Solidity/Missing.lean"}]
        with self.assertRaisesRegex(ValueError, "missing mapped"):
            recovery.validate_census(self.scope, self.census)

    def test_lost_declaration_refused(self):
        self.census["declarations"] = []
        with self.assertRaisesRegex(ValueError, "count"):
            recovery.validate_census(self.scope, self.census)

    def test_inflated_proof_coverage_refused(self):
        self.census["counts"]["joint_witnesses_verified"] = 1
        with self.assertRaisesRegex(ValueError, "proof coverage"):
            recovery.validate_census(self.scope, self.census)

    def test_bulk_output_inside_repository_refused(self):
        root = SCRIPTS.parents[3]
        with self.assertRaisesRegex(ValueError, "H44"):
            recovery.recover(root, root / "generated-evidence")


if __name__ == "__main__":
    unittest.main()
