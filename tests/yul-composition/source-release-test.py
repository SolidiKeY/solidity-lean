"""Fail-closed dependency-selection controls; no Lean execution."""
import importlib.util
from pathlib import Path
import unittest
import json
import subprocess
import tempfile

path = Path(__file__).resolve().parents[2] / 'scripts/yul-composition/source-release.py'
spec = importlib.util.spec_from_file_location('source_release', path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class SelectionTests(unittest.TestCase):
    def test_missing_transitive_source(self):
        graph = {'Controls': ['Lifecycle'], 'Lifecycle': ['World'], 'World': ['Monetary'], 'Monetary': []}
        self.assertEqual(module.required(['Controls'], graph, graph), ['Lifecycle', 'Monetary', 'World'])

    def test_missing_monetary_only(self):
        graph = {'Controls': ['Lifecycle'], 'Lifecycle': ['World'], 'World': ['Monetary'], 'Monetary': []}
        self.assertEqual(module.required(['Controls', 'Lifecycle', 'World'], graph, graph), ['Monetary'])

    def test_unchanged_dependency_uses_base(self):
        self.assertEqual(module.required(['Controls'], {'Controls': ['World']}, ['Controls']), [])

    def test_complete_selection(self):
        graph = {'Controls': ['World'], 'World': ['Monetary'], 'Monetary': []}
        self.assertEqual(module.required(list(graph), graph, graph), [])

    def test_import_cycle_terminates(self):
        graph = {'A': ['B'], 'B': ['A']}
        self.assertEqual(module.required(['A'], graph, graph), ['B'])

    def test_order_does_not_hide_missing_dependency(self):
        graph = {'A': ['C', 'B'], 'B': ['D'], 'C': ['D'], 'D': []}
        self.assertEqual(module.required(['A', 'C'], graph, graph), ['B', 'D'])


class HeaderTests(unittest.TestCase):
    def test_comments_and_multiple_imports(self):
        self.assertEqual(module.import_header("/- import Fake /- nested -/ -/\n  import Solidity.Source.World -- note\nimport A B\ndef x := 0\n"), ['Solidity.Source.World', 'A', 'B'])

    def test_string_comment_tokens_do_not_change_header(self):
        self.assertEqual(module.import_header('import A\ndef text := "/- unclosed"\n'), ['A'])

    def test_unsupported_header_refused(self):
        with self.assertRaises(ValueError):
            module.import_header('import\nSolidity.Source.World\n')


class CliTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.git('init', '-q')
        self.git('config', 'user.name', 'test')
        self.git('config', 'user.email', 'test@example.invalid')
        self.write('Solidity.lean', 'import Solidity.Controls\n')
        self.write('Solidity/Controls.lean', '  import Solidity.Source.World -- real dependency\n')
        self.write('Solidity/Source/World.lean', 'import Solidity.Source.Monetary\n')
        self.write('Solidity/Source/Monetary.lean', 'def old := 0\n')
        self.commit()
        self.base = self.git('rev-parse', 'HEAD')
        self.write('Solidity/Source/World.lean', 'import Solidity.Source.Monetary\ndef changed := 1\n')
        self.write('Solidity/Source/Monetary.lean', 'def wide := 2\n')
        self.commit()

    def tearDown(self):
        self.temp.cleanup()

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True).strip()

    def write(self, name, text):
        p = self.root / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)

    def commit(self):
        self.git('add', '.')
        self.git('commit', '-qm', 'fixture')

    def run_cli(self, selection=None):
        args = ['python3', str(path), '--base', self.base, '--output', str(self.root/'report.json')]
        if selection is not None:
            self.write('selection.json', json.dumps(selection))
            args += ['--selection', str(self.root/'selection.json')]
        result = subprocess.run(args, cwd=self.root, capture_output=True, text=True)
        return result.returncode, json.loads((self.root/'report.json').read_text())

    def test_standalone_control_rejected(self):
        rc, report = self.run_cli(['Solidity.Controls'])
        self.assertEqual(rc, 1)
        self.assertEqual(report['missingChangedDependencies'], ['Solidity.Source.Monetary', 'Solidity.Source.World'])

    def test_complete_changed_packet(self):
        rc, report = self.run_cli()
        self.assertEqual(rc, 0)
        self.assertTrue(report['selectionComplete'])

    def test_dirty_unchanged_intermediate_rejected(self):
        self.write('Solidity/Controls.lean', 'def erased := 1\n')
        rc, report = self.run_cli(['Solidity.Controls'])
        self.assertEqual(rc, 1)
        self.assertIn('Solidity/Controls.lean', report['staleSources'])
        self.assertIn('Solidity.Source.World', report['missingChangedDependencies'])

    def test_untracked_selection_rejected(self):
        self.write('Solidity/Untracked.lean', 'def unknown := 1\n')
        rc, report = self.run_cli(['Solidity.Untracked'])
        self.assertEqual(rc, 1)
        self.assertEqual(report['unknownModules'], ['Solidity.Untracked'])

    def test_missing_local_import_rejected(self):
        self.write('Solidity/Controls.lean', 'import Solidity.Source.Missing\n')
        self.commit()
        rc, report = self.run_cli(['Solidity.Controls'])
        self.assertEqual(rc, 1)
        self.assertEqual(report['missingLocalImports'], ['Solidity.Source.Missing'])

    def test_rename_destination_included(self):
        self.git('mv', 'Solidity/Source/Monetary.lean', 'Solidity/Source/Money.lean')
        self.write('Solidity/Source/World.lean', 'import Solidity.Source.Money\ndef changed := 1\n')
        self.commit()
        rc, report = self.run_cli(['Solidity.Source.World'])
        self.assertEqual(rc, 1)
        self.assertIn('Solidity.Source.Money', report['missingChangedDependencies'])


if __name__ == '__main__':
    unittest.main()
