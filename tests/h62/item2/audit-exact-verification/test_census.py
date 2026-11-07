"""Regression cases for actual census-review omissions and frozen fidelity."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location("census", ROOT / "scripts/h62/item2/audit-exact-verification/census.py")
CENSUS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CENSUS)


class CensusRegressions(unittest.TestCase):
    def test_comments_attributes_equations_and_root_names(self):
        source = ("namespace Outer\nvariable {a : Nat}\n"
                  "/- hidden /- theorem fake : False := bad -/ -/\n"
                  "@[simp] theorem visible (h : a = a) : a = a := h\n"
                  "theorem equations : (n : Nat) → n = n\n  | n => rfl\n"
                  "theorem _root_.Real.name : True := trivial\nend Outer\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Input.lean"
            path.write_text(source)
            rows = CENSUS.declarations(path, ["exact-verification"], root)
        self.assertEqual([r["name_candidate"] for r in rows], ["Outer.visible", "Outer.equations", "Real.name"])
        self.assertNotIn("=>", rows[1]["source_signature"])
        self.assertEqual(rows[0]["lexical_variables"], ["variable {a : Nat}"])

    def test_escaped_newlines_preserve_offsets_and_lines(self):
        source = 'def value := "abc' + chr(92) + chr(10) + ' def"\ntheorem next : True := trivial\n'
        clean = CENSUS.mask(source)
        self.assertEqual(len(clean), len(source))
        self.assertEqual([i for i,c in enumerate(clean) if c == "\n"],
                         [i for i,c in enumerate(source) if c == "\n"])

    def test_default_binder_value_is_not_proof_separator(self):
        source = "theorem checked (n : Nat := 0) : n = n := by rfl"
        end = CENSUS.signature_end(source, len("theorem"))
        self.assertEqual(source[:end], "theorem checked (n : Nat := 0) : n = n ")


if __name__ == "__main__": unittest.main()
