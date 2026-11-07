#!/usr/bin/env python3
"""Regression for reviewed frozen-source scanner failure modes; no Lean claim."""
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch
spec = importlib.util.spec_from_file_location("census", Path(__file__).with_name("census.py"))
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)

class FrozenScannerTests(unittest.TestCase):
    def test_result_let_with_inline_proof(self):
        source = """namespace X
variable {n : Nat}
theorem t (h : n < 4) :
 let ha : n < 5 := by have x := h; omega
 let k := n+1
 k < 6 := by omega
end X
"""
        with patch.object(census.subprocess, "check_output", return_value="commit author subject"):
            rows = census.declarations("fixture", source)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["name"], "X.t")
        self.assertTrue(rows[0]["signature"].endswith("k < 6"))
        self.assertIn("by have x := h; omega", rows[0]["signature"])
        self.assertEqual(rows[0]["section_context"], ["variable {n : Nat}"])

    def test_comments_and_strings_do_not_add_declarations(self):
        source = 'namespace X\n/- theorem ghost : False := by /- nested -/ -/\ndef x := "theorem hidden := fake"\n-- theorem hidden2\ntheorem real : True := by trivial\nend X\n'
        with patch.object(census.subprocess, "check_output", return_value="commit author subject"):
            rows = census.declarations("fixture", source)
        self.assertEqual([r["name"] for r in rows], ["X.real"])

    def test_duplicate_map_rows_fail(self):
        with self.assertRaises(AssertionError):
            census.module_paths("| `Backend/AbiEntry/Interface.lean` | text |\n| `Backend/AbiEntry/Interface.lean` | text |")

    def test_frozen_declarations_are_exactly_once(self):
        paths = census.module_paths(census.frozen(census.MAP))
        rows = [r for p in paths for r in census.declarations(p, census.frozen(p))]
        self.assertEqual(len(paths), 24)
        self.assertEqual(len(rows), 177)
        self.assertEqual(len({r["name"] for r in rows}), 177)
        for row in rows:
            self.assertFalse(row["signature"].endswith("by have h"), row["name"])
            self.assertEqual(row["owner"], "solidity-v12-v17-20261031/v13-abi-world")

if __name__ == "__main__": unittest.main()
