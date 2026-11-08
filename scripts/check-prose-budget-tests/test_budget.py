import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "check-prose-budget"
MODULE = runpy.run_path(str(SCRIPT))


class ScannerTests(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        source = '\n'.join([
            'def x := "-- /- fake -/"',
            'def y := r##"/- " -- fake"##',
            "def c := '\"'",
            'def «/- hidden -/» := 1',
            '/- outer',
            '  /- nested -/',
            '',
            'end -/ -- same line',
            '-- tail',
        ])
        self.assertEqual(MODULE['comment_lines'](source), (5, 0))

    def test_interpolation(self):
        self.assertEqual(MODULE['comment_lines']('def x := s!"{"--"}"'), (0, 0))
        self.assertEqual(MODULE['comment_lines']('def x := s!"{ /- real -/ 1 }"'), (1, 0))
        self.assertEqual(MODULE['comment_lines']('s!"{s!"{ /-- nested -/ 1 }"}"'), (1, 1))
        self.assertEqual(MODULE['comment_lines']('s!"{{ /- literal -/ }}"'), (0, 0))

    def test_docstrings(self):
        self.assertEqual(MODULE['comment_lines']('/-- docs\n/- nested -/\n-/\n/-! module -/'), (4, 4))
        self.assertEqual(MODULE['comment_lines']('/- plain /-- doc -/ end -/'), (1, 1))
        self.assertEqual(MODULE['comment_lines']('"escaped \\\" /- fake -/" -- real'), (1, 0))
        self.assertEqual(MODULE['comment_lines']('-- no final newline'), (1, 0))


class AcceptanceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'docs/guide').mkdir(parents=True)
        (self.root / 'Solidity/Area').mkdir(parents=True)
        (self.root / 'docs/guide/a.md').write_text('one\ntwo')
        (self.root / 'Solidity/Area/A.lean').write_text('/-- H13 G2 H14 -/\ndef x := "H99" -- GH1 XH2 H3x\n')
        self.baseline = self.root / 'baseline.json'
        self.initial = MODULE['counts'](self.root)
        self.baseline.write_text(json.dumps(self.initial))

    def run_script(self, *args):
        return subprocess.run([sys.executable, str(SCRIPT), '--root', str(self.root),
                               '--baseline', str(self.baseline), *args], capture_output=True, text=True)

    def test_counts_and_check(self):
        self.assertEqual(self.initial['docs/guide']['docs_lines'], 2)
        self.assertEqual(self.initial['Solidity/Area'], dict(docs_lines=0, comment_lines=2, docstring_lines=1, process_ids=4))
        self.assertEqual(self.run_script().returncode, 0)

    def test_never_raise_and_no_partial_write(self):
        for update in ((), ('--update',)):
            with self.subTest(update=update):
                before = self.baseline.read_bytes()
                (self.root / 'docs/guide/a.md').write_text('one\ntwo\nthree\n')
                self.assertEqual(self.run_script(*update).returncode, 1)
                self.assertEqual(self.baseline.read_bytes(), before)
        (self.root / 'docs/guide/a.md').write_text('one')
        (self.root / 'Solidity/Area/A.lean').write_text('-- H13 H14 G2 H99 H100')
        self.assertEqual(self.run_script('--update').returncode, 1)
        self.assertEqual(self.baseline.read_bytes(), before)

    def test_lower_and_deleted_areas(self):
        (self.root / 'docs/guide/a.md').unlink()
        self.assertEqual(self.run_script('--update').returncode, 0)
        self.assertEqual(json.loads(self.baseline.read_text())['docs/guide']['docs_lines'], 0)
        (self.root / 'docs/guide/a.md').write_text('back')
        self.assertEqual(self.run_script().returncode, 1)

    def test_new_area_zero_budget(self):
        (self.root / 'docs/new').mkdir()
        (self.root / 'docs/new/a.md').write_text('new')
        self.assertEqual(self.run_script('--update').returncode, 1)

    def test_missing_source_tree(self):
        before = self.baseline.read_bytes()
        (self.root / 'docs/guide/a.md').unlink()
        (self.root / 'docs/guide').rmdir()
        (self.root / 'docs').rmdir()
        self.assertEqual(self.run_script('--update').returncode, 2)
        self.assertEqual(self.baseline.read_bytes(), before)

    def test_invalid_and_missing_baseline(self):
        self.baseline.write_text('{"area": {"docs_lines": true}}')
        self.assertEqual(self.run_script('--update').returncode, 2)
        self.baseline.unlink()
        self.assertEqual(self.run_script('--update').returncode, 2)


if __name__ == '__main__':
    unittest.main()
