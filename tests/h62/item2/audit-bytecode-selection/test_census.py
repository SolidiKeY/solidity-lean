"""Adversarial lexical fixtures; these do not test Lean semantics."""
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch
import tempfile

ROOT = Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location("census", ROOT / "scripts/h62/item2/audit-bytecode-selection/census.py")
census = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(census)


class CensusTests(unittest.TestCase):
    def test_nested_comments_strings_and_sections(self):
        source = '''/- theorem ghost : False := /- nested -/ ignored -/
namespace A
section
variable (p : Prop)
-- theorem ghost2 : False := by contradiction
@[simp] theorem quoted (h : ":=" = ":=") : True := by trivial
end
namespace B
theorem negative (h : False) : False := h
end B
end A
'''
        rows = census.declarations(source)
        self.assertEqual([x["name_candidate"] for x in rows], ["A.quoted", "A.B.negative"])
        self.assertIn('":=" = ":="', rows[0]["signature"])
        self.assertEqual(rows[1]["status"], "uncovered")
        for row in rows:
            exact = source.encode()[row["byte_start"]:row["byte_end"]]
            self.assertEqual(exact.decode(), row["signature"])

    def test_delimiter_inside_dependent_binder(self):
        rows = census.declarations("theorem t (h : (let n := 2; n) = 2) : True := by trivial\n")
        self.assertIn("n := 2", rows[0]["signature"])
        self.assertTrue(rows[0]["signature"].endswith(": True "))

    def test_module_map_row_removal_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            target = repo / census.MAP
            target.parent.mkdir(parents=True)
            target.write_text("| `Backend/Selection/Interface.lean` | first |\n")
            frozen = target.read_bytes() + b"| `Backend/Selection/InterfaceV2.lean` | second |\n"
            with patch.object(census.subprocess, "check_output", return_value=frozen):
                with self.assertRaisesRegex(ValueError, "frozen module map"):
                    census.mapped_paths(repo)

    def test_fail_closed(self):
        for source in ["/- unfinished", 'def x := "unterminated', "theorem absent : True"]:
            with self.assertRaises(ValueError):
                census.declarations(source)


if __name__ == "__main__":
    unittest.main()
