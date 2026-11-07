#!/usr/bin/env python3
"""Adversarial checks for source census omissions and signature corruption."""
import tempfile
from pathlib import Path
from unittest.mock import patch
import unittest
import census


class CensusTests(unittest.TestCase):
    def test_comments_strings_and_nested_assignments(self):
        source = '''/- theorem fake : False := by /- lemma nested -/ -/
namespace N
-- theorem hidden : False := by
private theorem helper (x : Nat := 1) : x = x := rfl
theorem visible (s : String) (h : s = "theorem fake := ") : s = s := rfl
end N
'''
        rows = census.declarations(source, "fixture")
        self.assertEqual([r["name"] for r in rows], ["N.helper", "N.visible"])
        self.assertEqual(rows[0]["signature"], "private theorem helper (x : Nat := 1) : x = x ")
        self.assertIn('"theorem fake := "', rows[1]["signature"])
        self.assertNotIn("witness_status", rows[1])

    def test_fail_closed(self):
        cases = ["namespace N\nprotected theorem t : True := trivial\nend N\n",
                 "namespace N\nnamespace M\ntheorem t : True := trivial\nend M\nend N\n",
                 "namespace N\nsection S\ntheorem t : True := trivial\nend S\nend N\n",
                 "namespace N\ntheorem t : True\nend N\n"]
        for case in cases:
            with self.subTest(case=case), self.assertRaises(ValueError):
                census.declarations(case, "fixture")

    def test_section_variables_and_return_premises_preserved(self):
        source = "namespace N\nvariable {C : Type}\ntheorem t (x : C) : (x = x) → True := fun _ => trivial\nend N\n"
        row, = census.declarations(source, "fixture")
        self.assertEqual(row["section_variables"], ["variable {C : Type}"])
        self.assertIn("→ True", row["signature"])
        self.assertEqual(row["signature_sha256"], census.digest(row["signature"].encode()))

    def test_apostrophe_identifier(self):
        row, = census.declarations("namespace N\ntheorem foo' : True := trivial\nend N\n", "fixture")
        self.assertEqual(row["name"], "N.foo'")

    def test_next_assignment_cannot_repair_missing_assignment(self):
        with self.assertRaises(ValueError):
            census.declarations("namespace N\ntheorem a : True\ntheorem b : True := trivial\nend N\n", "fixture")

    def test_dirty_file_cannot_be_labeled_frozen(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/"file.lean"
            path.write_bytes(b"changed")
            with patch("census.subprocess.run") as run:
                run.return_value.stdout = b"frozen"
                with self.assertRaises(ValueError): census.frozen_bytes(Path(tmp), "file.lean")

    def test_namespace_and_multiline_variable_fail_closed(self):
        cases = ["theorem outside : True := trivial\nnamespace N\nend N\n",
                 "namespace N\nend N\ntheorem outside : True := trivial\n",
                 "namespace N\nvariable\n {C : Type}\ntheorem t : True := trivial\nend N\n",
                 "namespace N\nvariable {C : Type}\n {x : C}\ntheorem t : True := trivial\nend N\n"]
        for case in cases:
            with self.subTest(case=case), self.assertRaises(ValueError):
                census.declarations(case, "fixture")

    def test_let_inside_conclusion_is_part_of_signature(self):
        source="namespace N\ntheorem t (x : Nat) : x = (let y := x; y) := rfl\ntheorem u (x : Nat) : x =\n  let y := x\n  let z := y\n  z := rfl\nend N\n"
        first,second=census.declarations(source,"fixture")
        self.assertEqual(first["signature"], "theorem t (x : Nat) : x = (let y := x; y) ")
        self.assertTrue(second["signature"].endswith("  let z := y\n  z "))

    def test_exact_published_scheduling_change_only(self):
        old = b"/- doc -/\nnamespace Solidity.Backend.Scalar\ntheorem a : True := trivial\nend Solidity.Backend.Scalar\n"
        current = old.replace(b"-/\nnamespace", b"-/\n" + census.SCHEDULING_EDIT + b"namespace", 1)
        self.assertTrue(census.scheduling_only_change(census.SCHEDULING_PATH, old, current))
        self.assertFalse(census.scheduling_only_change("other.lean", old, current))
        self.assertFalse(census.scheduling_only_change(census.SCHEDULING_PATH, old, current.replace(b"True", b"False")))
        self.assertFalse(census.scheduling_only_change(census.SCHEDULING_PATH, old, current.replace(b"async false", b"async true")))
        a = census.declarations(old.decode(), "fixture")
        b = census.declarations(current.decode(), "fixture")
        self.assertEqual([r["signature"] for r in a], [r["signature"] for r in b])

    def test_unterminated_comment(self):
        with self.assertRaises(ValueError): census.mask("/-")


if __name__ == "__main__": unittest.main()
