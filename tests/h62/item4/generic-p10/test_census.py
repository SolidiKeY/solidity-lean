"""Adversarial scanner checks; these are external Python tests, not Lean proofs."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location('census', ROOT/'scripts/h62/item4/generic-p10/census.py')
C = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(C)


class CensusTests(unittest.TestCase):
    def scan(self, text):
        return C.declarations(text, 'Fixture.lean')

    def test_nested_comments_and_fake_commands(self):
        text = '/- outer /- inner -/\ntheorem fake : False := by\n-/\n' \
               'def text : String := "theorem fake := /-"\n' \
               '-- theorem fake : False := by\n' \
               'theorem real : True := by trivial\n'
        self.assertEqual([r['name'] for r in self.scan(text)], ['text', 'real'])

    def test_default_binders_and_result_lets(self):
        text = 'theorem t (n : Nat := 3) :\n  let m := n; m = n := by rfl\n'
        self.assertEqual(self.scan(text)[0]['statement'], text.split(' := by')[0])

    def test_nested_lets_and_structure_updates(self):
        text = 'theorem t : let a := (let b := 1; b); {x := a}.x = a := by rfl\n'
        self.assertEqual(self.scan(text)[0]['statement'], text.split(' := by')[0])

    def test_proof_change_preserves_statement_hash(self):
        a = self.scan('theorem t : True := by trivial\n')[0]
        b = self.scan('theorem t : True := True.intro\n')[0]
        self.assertEqual(a['statement_sha256'], b['statement_sha256'])
        self.assertNotEqual(a['declaration_sha256'], b['declaration_sha256'])

    def test_premise_change_rejected(self):
        a = self.scan('theorem t (h : True) : True := h\n')[0]
        b = self.scan('theorem t (h : False) : True := False.elim h\n')[0]
        self.assertNotEqual(a['statement_sha256'], b['statement_sha256'])

    def test_anonymous_controls_not_dropped(self):
        rows = self.scan('example : True := by trivial\nexample : False → False := id\n')
        self.assertEqual([r['name'] for r in rows], ['@example-0001', '@example-0002'])

    def test_comment_or_default_change_is_detected(self):
        a = self.scan('theorem t (n : Nat := 1) /- keep -/ : n=n := rfl\n')[0]
        b = self.scan('theorem t (n : Nat := 2) /- keep -/ : n=n := rfl\n')[0]
        self.assertNotEqual(a['statement_sha256'], b['statement_sha256'])

    def test_unterminated_input_refused(self):
        for text in ['/- unfinished', 'def s := "unfinished']:
            with self.assertRaises(ValueError): self.scan(text)

    def test_unbalanced_signature_refused(self):
        with self.assertRaises(ValueError): self.scan('theorem t (n : Nat : True := by trivial\n')

    def test_unsupported_forms_refused(self):
        for text in ['  theorem t : True := by trivial\n', '@[simp] theorem t : True := by trivial\n']:
            with self.assertRaises(ValueError): self.scan(text)

    def test_char_literals_do_not_create_delimiters(self):
        row = self.scan("def c : Char := '('\ntheorem t : True := by trivial\n")
        self.assertEqual(len(row), 2)

    def test_duplicate_ids_refused(self):
        with self.assertRaises(ValueError):
            self.scan('theorem t : True := by trivial\ntheorem t : True := by trivial\n')

    def test_primed_names(self):
        self.assertEqual(self.scan("theorem t' : True := by trivial\n")[0]['name'], "t'")

    def test_signature_strings_are_preserved(self):
        text = 'theorem t : "a:=b" = "a:=b" := rfl\n'
        self.assertEqual(self.scan(text)[0]['statement'], text.rsplit(' :=', 1)[0])

    def test_local_anonymous_instance(self):
        row = self.scan('local instance : ReflBEq UInt256 where\n  rfl := by trivial\n')[0]
        self.assertEqual(row['kind'], 'instance')
        self.assertEqual(row['name'], '@instance-0001')

    def test_structure_field_weakening_changes_statement(self):
        a = self.scan('structure Decode : Prop where\n  decoded : True\n')[0]
        b = self.scan('structure Decode : Prop where\n  decoded : False\n')[0]
        self.assertNotEqual(a['statement_sha256'], b['statement_sha256'])

    def test_empty_family_refused(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with self.assertRaises(ValueError): C.census(root)
            (root/C.FAMILY).mkdir(parents=True)
            with self.assertRaises(ValueError): C.census(root)

    def test_expected_guard_output_is_hashed(self):
        a = '/-- info: t depends on axioms: [] -/\n#guard_msgs in\n#print axioms t\n'
        b = a.replace('[]', '[sorryAx]')
        rows = C.check_commands(a, 'Fixture.lean')
        self.assertEqual([r['command'] for r in rows], ['#guard_msgs', '#print'])
        self.assertNotEqual(rows[0]['source_sha256'], C.check_commands(b, 'Fixture.lean')[0]['source_sha256'])


if __name__ == '__main__': unittest.main()
