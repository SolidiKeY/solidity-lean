"""Regression boundaries for the migration surface-signature checker."""
import importlib.util, pathlib, unittest
root=pathlib.Path(__file__).resolve().parents[3]
spec=importlib.util.spec_from_file_location('statements',root/'scripts/h55/yul-artifact/statements.py')
statements=importlib.util.module_from_spec(spec)
spec.loader.exec_module(statements)

class StatementTests(unittest.TestCase):
    def test_nested_comments_and_unicode(self):
        source='/-- ignored theorem bogus : False := by /- nested -/ -/\ntheorem α (x : Nat := 1) : x = x := by rfl\n'
        self.assertEqual(statements.signatures(source),{'α#0':'theorem α (x : Nat := 1) : x = x'})

    def test_proof_changes_are_outside_signature(self):
        a='theorem p (h : True) : True := by exact h'
        b='theorem p (h : True) : True := by trivial'
        self.assertEqual(statements.signatures(a),statements.signatures(b))

    def test_premise_change_is_visible(self):
        a='theorem p (h : True) : True := by exact h'
        b='theorem p (h : False) : True := by cases h'
        self.assertNotEqual(statements.signatures(a),statements.signatures(b))

    def test_multiline_string_cannot_replace_theorem(self):
        real='theorem p : True := by trivial\n'
        quoted='def text : String := "\ntheorem p : True := by trivial\n"\n'
        self.assertNotEqual(statements.signatures(real),statements.signatures(quoted))
        self.assertEqual(statements.signatures(quoted),{})

    def test_top_level_let_type_refused(self):
        with self.assertRaises(ValueError):
            statements.signatures('theorem p : let x := 1; x = x := by rfl')
        with self.assertRaises(ValueError):
            statements.signatures('theorem p : have h := True; True := by trivial')

    def test_string_literal_in_signature_is_retained(self):
        source='theorem p : "a:=b" = "a:=b" := by rfl'
        self.assertEqual(statements.signatures(source),{'p#0':'theorem p : "a:=b" = "a:=b"'})

    def test_keyword_suffix_in_identifier_is_not_rejected(self):
        source='theorem p (outlet : True) : outlet = outlet := by rfl'
        self.assertEqual(len(statements.signatures(source)),1)

    def test_malformed_header_refused(self):
        with self.assertRaises(ValueError): statements.signatures('theorem p : True')
        with self.assertRaises(ValueError): statements.signatures('/- unterminated')

    def test_duplicate_local_names_are_retained(self):
        source='theorem p : True := by trivial\ntheorem p : False := by contradiction'
        self.assertEqual(len(statements.signatures(source)),2)

if __name__ == '__main__': unittest.main()
