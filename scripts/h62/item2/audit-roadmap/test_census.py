"""Acceptance checks for extraction fidelity, not Lean proofs."""
import unittest
from census import mask, scan

class CensusTests(unittest.TestCase):
    def test_comments_strings_and_mutual(self):
        src = '''/- namespace Wrong /- theorem fake : False := x -/ -/
namespace A
section
variable {T : Type}
mutual
private theorem t (x : T) (h : True) : True := h
end
end
end A
'''
        rows, _ = scan(src, "fixture.lean", "tools", "fixture")
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["source_qualified_name"], "A.t")
        self.assertEqual(rows[0]["visibility"], "private")
        self.assertIsNone(rows[0]["elaborated_name"])
        self.assertEqual(rows[0]["section_variable_context"], ["variable {T : Type}"])
        self.assertEqual(len(mask(src)), len(src))

    def test_signature_and_root_and_proof_definition(self):
        src = '''namespace A
def certificate : True := True.intro
theorem _root_.B.t (n : Nat := 0) : n = n := rfl
end A
'''
        rows, extra = scan(src, "fixture.lean", "tools", "fixture")
        self.assertEqual(rows[0]["source_qualified_name"], "B.t")
        self.assertEqual(rows[0]["signature"], "theorem _root_.B.t (n : Nat := 0) : n = n")
        self.assertEqual(extra[0]["source_qualified_name"], "A.certificate")

    def test_equational_theorem(self):
        src = "theorem t : (n : Nat) → n = n\n  | 0 => rfl\n  | n+1 => rfl\n"
        rows, _ = scan(src, "fixture.lean", "tools", "fixture")
        self.assertEqual(rows[0]["signature"], "theorem t : (n : Nat) → n = n")

    def test_anonymous_instance_binders(self):
        src = "namespace N\ninstance {T : Type} : Nonempty (Option T) := ⟨none⟩\ninstance : Nonempty Nat := ⟨0⟩\nend N\n"
        rows, extra = scan(src, "fixture.lean", "tools", "fixture")
        self.assertEqual(rows, [])
        self.assertTrue(all(r["source_qualified_name"] is None for r in extra))
        self.assertEqual([r["source_id"] for r in extra], ["fixture.lean:2", "fixture.lean:3"])

    def test_result_type_let_assignments(self):
        src = "theorem t : let x := 1; let y := x + 1; y = 2 := rfl\n"
        rows, _ = scan(src, "fixture.lean", "tools", "fixture")
        self.assertEqual(rows[0]["signature"], "theorem t : let x := 1; let y := x + 1; y = 2")

    def test_inline_attributes_and_deriving_commands(self):
        src = "namespace N\n@[inline] def f (n : Nat) : Nat := n\nderiving instance Repr for Nat\nend N\n"
        rows, extra = scan(src, "fixture.lean", "tools", "fixture")
        self.assertEqual(rows, [])
        self.assertEqual(extra[0]["source_qualified_name"], "N.f")
        self.assertIsNone(extra[1]["source_qualified_name"])
        self.assertEqual(extra[1]["source_form"], "deriving-instance-command")

    def test_unterminated_comment_fails_closed(self):
        with self.assertRaises(ValueError):
            mask("/- theorem t : False := x")

if __name__ == "__main__":
    unittest.main()
