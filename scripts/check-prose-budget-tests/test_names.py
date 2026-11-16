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

    def test_canonical_module_import_forms(self):
        for leading in ('', ' ', '\t'):
            for modifier in ('', 'public ', 'meta ', 'public meta '):
                for extra in ('', 'all '):
                    if modifier.startswith('public') and extra:
                        continue
                    with self.subTest(leading=leading, modifier=modifier, extra=extra):
                        source = (leading + 'module\nprelude\n' + leading + modifier +
                                  'import ' + extra + 'Solidity.H290.G17.Real -- G99 H99\n')
                        self.assertEqual(self.count(source), 3)
        self.assertEqual(self.count(' import Solidity.Lowering.G17.Real\n'), 0)
        self.assertEqual(self.count('import Lean\nimport Solidity.Lowering.G17.Real\n'), 0)
        self.assertEqual(M['process_ids']('module\nimport G17\n', REGISTRY | {'G17'}), 1)

    def test_invalid_module_import_forms_stay_counted(self):
        module = 'Solidity.Lowering.G17.Real'
        for source in ['public import ' + module, 'meta import ' + module,
                       'import all ' + module, 'module\npublic import all ' + module,
                       'module\npublic meta import all ' + module,
                       'module\nmeta public import ' + module,
                       'module\nmodule\nimport ' + module,
                       'prelude\nmodule\nimport ' + module,
                       'module\nimport ' + module + '\nmodule',
                       'module\nimport ' + module + '\nprelude',
                       'module\npublic! import ' + module,
                       'module\nmeta? import ' + module,
                       'module\nimport all! ' + module,
                       'module\npublic import Solidity.Lowering.«G17».Real',
                       'module\npublic import ' + module + ' trailing',
                       'module\npublic import ' + module + '.Missing']:
            with self.subTest(source=source):
                self.retained(source)

    def test_unknown_bare_imports_fail_closed(self):
        module = 'Solidity.Lowering.G17.Real'
        for name in ('module', 'prelude', 'public', 'meta', 'all', 'import',
                     'namespace', 'end', 'UnknownBareModule'):
            with self.subTest(name=name):
                self.retained('import ' + name + '\nimport ' + module + '\n')
                self.retained('import ' + module + '\nimport ' + name + '\n')
        for root in ('Init', 'Lean', 'Std'):
            self.assertEqual(self.count('import ' + root + '\nimport ' + module), 0)

    def test_header_modifiers_do_not_change_namespace_policy(self):
        source = ('module\npublic /- G99 H99 -/ meta import Solidity.G17.G18.Real\n'
                  'namespace Solidity.G17.G18\nend Solidity.G17.G18\n')
        self.assertEqual(self.count(source), 6)
        self.retained('def x := 1\nmodule\npublic import Solidity.G17.G18.Real\n')

    def test_import_retained_boundaries(self):
        for source in ['import Solidity.Lowering.G17.Fake\n',
                       'import Solidity.Lowering.G17.Real.More\n',
                       'import Solidity.G17.G999.Real\n',
                       'import Solidity.Lowering.«G17».Real\n',
                       'import Solidity.Lowering.G17.Real trailing\n',
                       'import Solidity.Lowering.G17.Real Solidity.G17.G18.Real\n',
                       'def x := 1\nimport Solidity.Lowering.G17.Real\n',
                       ' def x := 1\nimport Solidity.Lowering.G17.Real\n',
                       'prelude\nprelude\nimport Solidity.Lowering.G17.Real\n',
                       'import Solidity.Lowering.G17.Real\nprelude\n',
                       'import G17\n', 'import _root_.Solidity.G17.G18.Real\n']:
            with self.subTest(source=source):
                self.retained(source)

    def test_namespace_pairs_remain_pending(self):
        for name in ['Solidity.Lowering.G17', 'Solidity.Lowering.G17.Real',
                     'Solidity.G17.G18', 'Solidity.H290.G17']:
            with self.subTest(name=name):
                self.retained(f'namespace {name}\nend {name}\n')
        self.assertEqual(self.count('namespace Solidity.Lowering.G17 -- H1 G1\n'
                                    'end Solidity.Lowering.G17 /- G2 H2 -/\n'), 6)

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
        self.retained(source)

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
                       'import Imported.Macros\nwrap\n' + pair,
                       'import Imported.Macros\n wrap\n' + pair,
                       'import Imported.Macros\n\twrap\n' + pair,
                       'import Imported.Macros\ndef x : Nat := by exact 1\n wrap\n' + pair,
                       'import Imported.Macros\ndef x := (1)\n wrap\n' + pair,
                       'import Imported.Macros\ndef!\n' + pair,
                       'import Imported.Macros\ndef?\n' + pair,
                       "import Imported.Macros\ndef'\n" + pair,
                       'import Imported.Macros\n#print!\n' + pair,
                       'import Imported.Macros\ndef.G17\n' + pair,
                       'import Imported.Macros\n rw\n' + pair,
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

    def test_declaration_context_remains_conservative(self):
        pair = 'namespace Solidity.Lowering.G17\n{body}\nend Solidity.Lowering.G17\n'
        for body in ['def x := 1', 'private def x := 1', '@[simp] theorem t : True := by trivial',
                     'variable (x : Nat)', '#check Nat', 'open Nat', 'set_option pp.all true']:
            with self.subTest(body=body):
                self.retained(pair.format(body=body))

    def test_certain_header_import_and_uncertain_body(self):
        source = ('import Solidity.Lowering.G17.Real\n'
                  'namespace Solidity.Lowering.G17\n'
                  'def x := unknownImportedTerm\n'
                  'end Solidity.Lowering.G17\n')
        self.assertEqual(self.count(source), 2)
        self.retained(source.replace('import Solidity.Lowering.G17.Real',
                                     'import Solidity.Lowering.G17.Unknown'))

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
            counts = M['counts'](root);self.assertEqual(counts['Solidity/Area']['process_ids'], 4)
            self.assertEqual(counts['Solidity/Area']['comment_lines'], 1)
            self.assertEqual(counts['Solidity/Area']['docstring_lines'], 0)
            baseline.write_text(json.dumps(counts));before = baseline.read_bytes()
            lean.write_text(source + '-- G18\n')
            for flag in [[], ['--update']]:
                result = subprocess.run([sys.executable, '-B', str(SCRIPT), '--root', str(root), *flag],
                                        text=True, capture_output=True)
                self.assertEqual(result.returncode, 1)
                self.assertIn('process_ids: 5 > 4', result.stderr)
                self.assertEqual(baseline.read_bytes(), before)


if __name__ == '__main__':
    unittest.main()
