import importlib.util
from pathlib import Path
import unittest
import tempfile

ROOT = Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location("census", ROOT / "scripts/h62/item4/generic-memorycopies/census.py")
census = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(census)

class CensusTests(unittest.TestCase):
    def test_nested_comments_strings_and_binder_assignment(self):
        text = '\n/- /- nested -/ theorem fake : False := nope -/\nprivate theorem real (x : Nat := 2) : x = x := by rfl\ndef label : String := "theorem fake : False := nope"\n'
        rows = census.declarations(text)
        self.assertEqual([r['name'] for r in rows], ['real', 'label'])
        self.assertEqual(rows[0]['header'], 'private theorem real (x : Nat := 2) : x = x ')
    def test_unicode_byte_offsets(self):
        text = '-- α\ntheorem one : True := by trivial\n'
        row = census.declarations(text)[0]
        self.assertEqual(text.encode()[row['byte_start']:row['byte_end']].decode(), row['header'])
    def test_fail_closed(self):
        with self.assertRaises(ValueError):
            census.declarations('theorem unfinished : True\nend X\n')
        with self.assertRaises(ValueError):
            census.mask('/- unfinished')
    def test_header_change_is_detected(self):
        a = census.declarations('theorem t : 1 = 1 := rfl')[0]
        b = census.declarations('theorem t : 2 = 2 := rfl')[0]
        self.assertNotEqual(a['header_sha256'], b['header_sha256'])
    def test_type_level_lets(self):
        text = 'theorem t :\n  let x := 1\n  let y := x + 1\n  y = 2 := by rfl'
        row = census.declarations(text)[0]
        self.assertEqual(row['header'], text[:text.rindex(':=')])
    def test_nested_file_is_included(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            nested = root / census.FAMILY / 'Nested'
            nested.mkdir(parents=True)
            (nested / 'Control.lean').write_text('theorem kept : True := by trivial')
            self.assertEqual(census.census(root)['counts']['files'], 1)
    def test_match_in_statement(self):
        text = 'theorem t :\n  match true with\n  | true => True\n  | false => False := by trivial'
        self.assertEqual(census.declarations(text)[0]['header'], text[:text.rindex(':=')])
    def test_equations_and_where(self):
        rows = census.declarations('def f : Nat → Nat\n  | n => n\nstructure Input where\n  value : Nat\n')
        self.assertEqual(rows[0]['header'], 'def f : Nat → Nat\n  ')
        self.assertEqual(rows[1]['header'], 'structure Input')
        with self.assertRaises(ValueError):
            census.declarations('theorem bad (x : Nat] : True := by trivial')
    def test_body_change_preserves_statement_hash(self):
        a = census.declarations('theorem t : True := by trivial')[0]
        b = census.declarations('theorem t : True := True.intro')[0]
        self.assertEqual(a['header_sha256'], b['header_sha256'])

if __name__ == '__main__':
    unittest.main()
