import json
from pathlib import Path
import re
import runpy
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'check-prose-budget'
M = runpy.run_path(str(SCRIPT))
REGISTRY = {'Solidity.Lowering.G17.Real', 'Solidity.G17.G18.Real',
            'Solidity.H290.G17.Real'}


class RegisteredNamesTests(unittest.TestCase):
    def count(self, source):
        return M['process_ids'](source, REGISTRY)

    def retained(self, source):
        self.assertEqual(self.count(source), len(re.findall(r'\b[GH][0-9]+\b', source)))

    def test_registered_import(self):
        self.assertEqual(self.count('import Solidity.Lowering.G17.Real\n'), 0)
        self.assertEqual(self.count('import Solidity.G17.G18.Real\n'), 0)
        self.assertEqual(self.count('import Solidity.H290.G17.Real\n'), 1)
        self.assertEqual(self.count('import Solidity.G17.G18.Real -- G17 H290\n'), 2)

    def test_import_retained_boundaries(self):
        for source in ['import Solidity.Lowering.G17.Fake\n',
                       'import Solidity.Lowering.G17.Real.More\n',
                       'import Solidity.G17.G999.Real\n',
                       'import Solidity.Lowering.«G17».Real\n',
                       'import Solidity.Lowering.G17.Real trailing\n',
                       'import Solidity.Lowering.G17.Real Solidity.G17.G18.Real\n',
                       'def x := 1\nimport Solidity.Lowering.G17.Real\n',
                       ' import Solidity.Lowering.G17.Real\n',
                       ' def x := 1\nimport Solidity.Lowering.G17.Real\n',
                       'prelude\nprelude\nimport Solidity.Lowering.G17.Real\n',
                       'import Solidity.Lowering.G17.Real\nprelude\n',
                       'import G17\n', 'import _root_.Solidity.G17.G18.Real\n']:
            with self.subTest(source=source):
                self.retained(source)

    def test_complete_namespace_pairs(self):
        for name in ['Solidity.Lowering.G17', 'Solidity.Lowering.G17.Real',
                     'Solidity.G17.G18', 'Solidity.H290.G17']:
            with self.subTest(name=name):
                self.assertEqual(self.count(f'namespace {name}\ndef x := 1\nend {name}\n'),
                                 2 if 'H290' in name else 0)
        self.assertEqual(self.count('namespace Solidity.Lowering.G17 -- H1 G1\n'
                                    'end Solidity.Lowering.G17 /- G2 H2 -/\n'), 4)

    def test_pair_retained_boundaries(self):
        for source in ['namespace Solidity.Lowering.G17\n',
                       'namespace Solidity.Lowering.G17\nend\n',
                       'namespace Solidity.Lowering.G17\nend G17\n',
                       'namespace Solidity.Lowering.G17\nend Solidity.G17.G18\n',
                       'namespace Solidity.Lowering.G17\nend Solidity.Lowering.G17\nend\n',
                       'namespace Solidity.G17.G999\nend Solidity.G17.G999\n',
                       'namespace _root_.Solidity.Lowering.G17\nend _root_.Solidity.Lowering.G17\n',
                       'namespace Solidity.Lowering.«G17»\nend Solidity.Lowering.«G17»\n',
                       'namespace G17\nend G17\n',
                       ' namespace Solidity.Lowering.G17\n end Solidity.Lowering.G17\n']:
            with self.subTest(source=source):
                self.retained(source)

    def test_nested_and_relative_retained(self):
        for opening, closing in [('noncomputable section', 'end'),
                                 ('public section', 'end'),
                                 ('@[expose] public noncomputable section', 'end'),
                                 ('namespace Outer', 'end Outer'),
                                 ('section S', 'end S'), ('section', 'end'),
                                 ('mutual', 'end')]:
            self.retained(opening + '\nnamespace Solidity.Lowering.G17\n'
                          'end Solidity.Lowering.G17\n' + closing + '\n')
        source = ('namespace Solidity.Lowering.G17\nnamespace Relative.G17\n'
                  'end Relative.G17\nend Solidity.Lowering.G17\n')
        self.assertEqual(self.count(source), 2)

    def test_prose_literals_and_references_retained(self):
        for source in ['-- import Solidity.Lowering.G17.Real\n',
                       '/- namespace Solidity.Lowering.G17\nend Solidity.Lowering.G17 -/',
                       '/-- G17 H290 /- G18 -/ -/',
                       'def s := "import Solidity.Lowering.G17.Real"',
                       'def s := r#"namespace Solidity.G17.G18\nend Solidity.G17.G18"#',
                       'def s := s!"G17 { /- H290 G18 -/ 1 }"',
                       'def s := s!"{m!"{ /- G17 -/ 1 }"}"',
                       '#check Solidity.Lowering.G17.Real.x',
                       'abbrev x := Solidity.Lowering.G17.Real.x',
                       '#check G17\n#check H290',
                       'def «namespace Solidity.G17» := 1',
                       'def name := `Solidity.Lowering.G17.Real']:
            with self.subTest(source=source):
                self.retained(source)

    def test_quotes_wrappers_and_malformed_retained(self):
        pair = 'namespace Solidity.Lowering.G17\nend Solidity.Lowering.G17\n'
        for source in ['`(command|\n' + pair + ')',
                       'def s := `(command| namespace Solidity.Lowering.G17)\n' + pair,
                       '#guard_msgs in\n' + pair,
                       '#with_exporting\n' + pair,
                       'import ImportedMacros\nwrap\n' + pair,
                       'include h in\n' + pair,
                       'omit h in\n' + pair,
                       ' #guard_msgs in\n' + pair,
                       '\tset_option pp.all true in\n' + pair,
                       ' @[expose] section\n' + pair,
                       '@[expose] section\n' + pair,
                       'set_option pp.all true in\n' + pair,
                       'set_option pp.all true\n in\n' + pair,
                       'set_option pp.all true /-\n-/ in\n' + pair,
                       'open Nat\nin\n' + pair,
                       'open Nat in\n' + pair,
                       '(' + pair, pair + ')', pair + '/- unclosed',
                       'namespace Outer\nend\n' + pair,
                       'noncomputable section\n' + pair,
                       pair + '/- outer /- inner -/',
                       'import Solidity.Lowering.G17.Real\ndef x := "unclosed',
                       'import Solidity.Lowering.G17.Real\ndef s := s!"unclosed',
                       'import Solidity.Lowering.G17.Real\ndef s := s!"{1}',
                       'import Solidity.Lowering.G17.Real\ndef s := s!"{1"']:
            with self.subTest(source=source):
                self.retained(source)

    def test_known_declarations_stay_eligible(self):
        pair = 'namespace Solidity.Lowering.G17\n{body}\nend Solidity.Lowering.G17\n'
        for body in ['def x := 1', 'private def x := 1', '@[simp] theorem t : True := by trivial',
                     'variable (x : Nat)', '#check Nat', 'open Nat', 'set_option pp.all true']:
            with self.subTest(body=body):
                self.assertEqual(self.count(pair.format(body=body)), 0)

    def test_registry_roots_only(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / 'Solidity.lean').write_text('import Solidity.Lowering.G17.Real\n')
            (root / 'SoliditySlowExamples.lean').write_text('import Solidity.G17.G18.Real\n')
            (root / 'Unregistered.lean').write_text('import Solidity.Fake.G999.X\n')
            self.assertEqual(M['registered_modules'](root), REGISTRY - {'Solidity.H290.G17.Real'})
            self.assertEqual(M['process_ids']('import Solidity.Fake.G999.X', M['registered_modules'](root)), 1)

    def test_cli_shrink_only_and_other_metrics(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d); (root / 'docs').mkdir(); (root / 'Solidity/Area').mkdir(parents=True)
            (root / 'Solidity.lean').write_text('import Solidity.Lowering.G17.Real\n')
            lean = root / 'Solidity/Area/A.lean'
            source = ('import Solidity.Lowering.G17.Real\nnamespace Solidity.Lowering.G17\n'
                      '-- G17 H290\nend Solidity.Lowering.G17\n')
            lean.write_text(source)
            baseline = root / 'scripts/prose-baseline.json';baseline.parent.mkdir()
            counts = M['counts'](root);self.assertEqual(counts['Solidity/Area']['process_ids'], 2)
            self.assertEqual(counts['Solidity/Area']['comment_lines'], 1)
            self.assertEqual(counts['Solidity/Area']['docstring_lines'], 0)
            baseline.write_text(json.dumps(counts));before = baseline.read_bytes()
            lean.write_text(source + '-- G18\n')
            for flag in [[], ['--update']]:
                result = subprocess.run([sys.executable, '-B', str(SCRIPT), '--root', str(root), *flag],
                                        text=True, capture_output=True)
                self.assertEqual(result.returncode, 1)
                self.assertIn('process_ids: 3 > 2', result.stderr)
                self.assertEqual(baseline.read_bytes(), before)


if __name__ == '__main__':
    unittest.main()
