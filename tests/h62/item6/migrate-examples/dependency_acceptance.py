#!/usr/bin/env python3
"""Negative controls for frozen-scope, explicit-header dependency accounting."""
import pathlib
import importlib.util
import copy
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'scripts/h62/item6/migrate-examples'))
import dependencies as deps


class HeaderTests(unittest.TestCase):
    def test_header_only_and_comments(self):
        source = '/- /- nested -/ import Wrong -/\nmodule\nprelude\npublic meta import A.B\nimport C\nimport D\n  theorem t : True := by\n    exact True.intro\n-- import Wrong\ndef x := "import Wrong"\n'
        self.assertEqual(deps.header_imports(source), ['A.B', 'C', 'D'])

    def test_directives_quoted_names_and_command_boundaries(self):
        self.assertEqual(deps.header_imports('import A\n  import B.C\nimport «quoted-name».D\nnamespace N\n'), ['A', 'B.C', '«quoted-name».D'])
        for body in ('@[simp] theorem t : True := True.intro', '#check Nat', '  mutual\nend'):
            self.assertEqual(deps.header_imports('import A\n' + body), ['A'])
        self.assertEqual(deps.module_path('«a.b».C'), 'a.b/C.lean')
        with self.assertRaises(ValueError):
            deps.header_imports('import A, B\n')


class ClosureTests(unittest.TestCase):
    def test_scope_vendor_and_missing_import_controls(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            def git(*args):
                return subprocess.check_output(['git', *args], cwd=root, stderr=subprocess.DEVNULL).decode().strip()
            def write(path, text):
                p = root / path
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(text)
            git('init', '-q')
            git('config', 'user.name', 'Dependency test')
            git('config', 'user.email', 'dependency-test@localhost')
            write('lakefile.toml', 'name = "fixture"\n[[lean_lib]]\nname = "Fixture"\nsrcDir = "vendor"\n')
            write('Solidity/Examples/A.lean', 'import Fixture.Core\nimport Lean.Test\nexample : True := True.intro\n')
            write('vendor/Fixture/Core.lean', 'def seven : Nat := 7\n')
            write('a.b/C.lean', 'def rightPath : Nat := 7\n')
            write('a/b/C.lean', 'import Wrong.Path\n')
            git('add', '.')
            git('commit', '-qm', 'frozen')
            base = git('rev-parse', 'HEAD')
            std = root / 'stdlib'
            write('stdlib/Init.olean', '')
            write('stdlib/Lean/Test.olean', '')
            with patch.object(deps, 'BASE', base):
                tree = deps.Tree(root, base)
                self.assertEqual(tree.resolve('«a.b».C', tree.dirs()), 'a.b/C.lean')
                data = deps.closure(root, base, std)
                self.assertEqual((data['scope_modules'], data['local_closure'], data['external_local_modules']), (1, 2, 1))
                self.assertEqual(data['stdlib_leaves'], ['Lean.Test'])
                self.assertEqual(data['unresolved_imports'], [])
                write('Solidity/Examples/Additional.lean', 'def extra := 8\n')
                git('add', 'Solidity/Examples/Additional.lean')
                git('commit', '-qm', 'new example outside frozen assignment')
                data = deps.closure(root, 'HEAD', std)
                self.assertEqual(data['scope_modules'], 1)
                self.assertEqual(data['local_closure'], 2)
                self.assertEqual(data['additional_examples_outside_original_scope'], ['Solidity/Examples/Additional.lean'])
                # Dirty working files do not contaminate a committed-tree census.
                write('Solidity/Examples/A.lean', 'import Missing.Dependency\n')
                self.assertEqual(deps.closure(root, 'HEAD', std)['unresolved_imports'], [])
                git('add', 'Solidity/Examples/A.lean')
                git('commit', '-qm', 'unresolved dependency')
                self.assertEqual(deps.closure(root, 'HEAD', std)['unresolved_imports'], ['Missing.Dependency'])
                git('rm', '-q', 'Solidity/Examples/A.lean')
                git('commit', '-qm', 'removed original')
                with self.assertRaisesRegex(ValueError, 'missing original scope'):
                    deps.closure(root, 'HEAD', std)


class ScopeFixtureTests(unittest.TestCase):
    def setUp(self):
        path = ROOT / 'scripts/h62/item6/migrate-examples/prepare-scoped-dump.py'
        spec = importlib.util.spec_from_file_location('scoped_dump', path)
        self.tool = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.tool)
        self.scope = {'base': deps.BASE, 'modules': [{'module': 'Solidity.Examples.A'}, {'module': 'Solidity.Examples.B'}]}
        self.report = {'base': deps.BASE, 'unresolved_imports': [], 'modules': self.scope['modules'] + [{'module': 'Solidity.Core'}]}
        self.template = 'import Lean\nimport SolidityExamples\n-- all declarations retained\n'

    def test_exact_scope_and_template_preservation(self):
        rendered = self.tool.render(self.template, self.scope, self.report)
        self.assertEqual(deps.header_imports(rendered), ['Lean', 'Solidity.Examples.A', 'Solidity.Examples.B'])
        self.assertTrue(rendered.endswith('-- all declarations retained\n'))
        self.assertEqual(rendered, self.tool.render(self.template, self.scope, self.report))

    def test_missing_extra_and_template_shape_refused(self):
        for modules in (self.report['modules'][1:], self.report['modules'] + [{'module': 'Solidity.Examples.New'}]):
            report = copy.deepcopy(self.report)
            report['modules'] = modules
            with self.assertRaisesRegex(ValueError, 'transitive example'):
                self.tool.render(self.template, self.scope, report)
        with self.assertRaisesRegex(ValueError, 'template import shape'):
            self.tool.render(self.template.replace('import SolidityExamples', 'import Other'), self.scope, self.report)
        scope = copy.deepcopy(self.scope)
        scope['modules'].append(scope['modules'][0])
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            self.tool.render(self.template, scope, self.report)


if __name__ == '__main__':
    unittest.main()
