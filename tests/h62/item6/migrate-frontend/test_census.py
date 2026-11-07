"""Negative controls for imports and the exact ownership boundary."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location('census', ROOT/'scripts/h62/item6/migrate-frontend/census.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)

class CensusControls(unittest.TestCase):
    def test_comments_and_string_imports_are_excluded(self):
        text = '/-\nimport False.Doc\n/- nested -/\n-/\nimport A.B C.D -- hi\n\n/-doc-/\nimport Lean\ndef x := "\nimport False.String\n"\nimport False.Body\n'
        self.assertEqual(c.imports(text), ['A.B','C.D','Lean'])
        self.assertEqual(len(c.mask(text)), len(text))
        self.assertEqual(c.mask(text).count('\n'), text.count('\n'))

    def test_quote_character_does_not_hide_following_theorem(self):
        text = "def quote : Char := '\"'\ntheorem retained : True := by trivial\n"
        self.assertIn('theorem retained', c.mask(text))

    def test_escape_nested_comment_and_all(self):
        self.assertEqual(c.imports('prelude\n/- one /- two -/ three -/\nimport all A\ndef x := "\\\""\n'), ['A'])

    def test_import_whitespace(self):
        self.assertEqual(c.imports('import\tA\nimport B\n'), ['A','B'])

    def test_malformed_import_fails_closed(self):
        with self.assertRaises(ValueError): c.imports('import A + B\n')

    def test_ownership_and_cycles_fail_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)
            (p/'Solidity/Frontend').mkdir(parents=True)
            (p/'Solidity/Frontend/A.lean').write_text('import Solidity.Frontend.B\n')
            (p/'Solidity/Frontend/B.lean').write_text('import Solidity.Frontend.A\n')
            owner={'items':[{'id':c.OWNER,'writeScope':'Solidity/Frontend/A.lean'}]}
            with self.assertRaises(ValueError): c.census(p, owner)
            owner['items'][0]['writeScope'] += '; Solidity/Frontend/B.lean'
            with self.assertRaisesRegex(ValueError, 'cycle'): c.census(p, owner)

    def test_transitive_external_closure_and_registration_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)
            (p/'Solidity/Frontend').mkdir(parents=True)
            (p/'Solidity/Frontend/A.lean').write_text('import Solidity.External\nexample : True := by trivial\n')
            (p/'Solidity/External.lean').write_text('import Lean\n')
            (p/'Solidity/Frontend/registration.json').write_text('{}\n')
            owner={'items':[{'id':c.OWNER,'writeScope':'Solidity/Frontend/A.lean; Solidity/Frontend/registration.json'}]}
            x=c.census(p,owner)
            self.assertEqual(x['topological_closure'],['Solidity.External','Solidity.Frontend.A'])
            self.assertEqual(x['external_local_modules'],['Solidity.External'])
            self.assertEqual(len(x['scope_files']),2)
            self.assertEqual(len(x['declaration_candidates']),1)

if __name__ == '__main__': unittest.main()
