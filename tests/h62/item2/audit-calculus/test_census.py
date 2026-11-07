"""Adversarial source-census controls from independent finder/skeptic reviews."""
import importlib.util
from pathlib import Path
import unittest

SCRIPT = Path(__file__).resolve().parents[4]/"scripts/h62/item2/audit-calculus/census.py"
spec = importlib.util.spec_from_file_location("census", SCRIPT)
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)


class CensusControls(unittest.TestCase):
    def test_nested_comments_and_strings_are_not_declarations(self):
        source = '\n/- theorem fake : False := /- nested -/ oops -/\ndef s := "theorem fake2 : False := oops"\ntheorem real : True := True.intro\n'
        rows = census.declarations(source, "fixture")
        self.assertEqual([r["source_name"] for r in rows], ["real"])

    def test_mutual_end_preserves_namespace(self):
        rows = census.declarations("namespace N\nmutual\ntheorem a : True := True.intro\nend\ntheorem b : True := True.intro\nend N\n", "fixture")
        self.assertEqual([r["source_name"] for r in rows], ["N.a", "N.b"])

    def test_type_let_is_retained(self):
        rows = census.declarations("theorem t : let code := 1; code = 1 := rfl\n", "fixture")
        self.assertEqual(rows[0]["signature"], "theorem t : let code := 1; code = 1")

    def test_multiline_global_assumptions_and_include(self):
        rows = census.declarations("namespace N\nvariable {C : Type}\n  (hleaf : C → Prop)\n  (global : ∀ x, hleaf x)\ninclude global\ntheorem t (x : C) : hleaf x := global x\nend N\n", "fixture")
        directives = "\n".join(rows[0]["section_directive_history"])
        self.assertIn("(global : ∀ x, hleaf x)", directives)
        self.assertIn("include global", directives)
        self.assertEqual(rows[0]["joint_witness"], "pending")

    def test_equation_style_signature(self):
        source = "theorem t : ∀ n : Nat, n = n\n  | n => rfl\n"
        self.assertEqual(census.declarations(source, "fixture")[0]["signature"], "theorem t : ∀ n : Nat, n = n")

    def test_scope_expansion(self):
        self.assertEqual(census.expand("Try{Plan,Whole}.lean"), ["TryPlan.lean", "TryWhole.lean"])


if __name__ == "__main__":
    unittest.main()
