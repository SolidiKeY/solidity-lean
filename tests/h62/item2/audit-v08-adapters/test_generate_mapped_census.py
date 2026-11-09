"""Guard mapped collector drift, stale imports and diagnostic output overwrite."""
import hashlib
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'scripts/h62/item2/audit-v08-adapters'))
spec = importlib.util.spec_from_file_location('mapped', ROOT / 'scripts/h62/item2/audit-v08-adapters/generate_mapped_census.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
TEMPLATE = (ROOT / module.TEMPLATE).read_text()
PATH = 'Solidity/Test.lean'
DATA = b'def test := 1\n'
SNAPSHOT = {'modules': [{'file': PATH, 'sha256': hashlib.sha256(DATA).hexdigest()}]}


class Generator(unittest.TestCase):
    def setup_repo(self, root):
        repo = Path(root) / 'repo'
        p = repo / PATH
        p.parent.mkdir(parents=True)
        p.write_bytes(DATA)
        t = repo / module.TEMPLATE
        t.parent.mkdir(parents=True)
        t.write_text(TEMPLATE)
        return repo

    def prepare(self, repo, snapshot=SNAPSHOT, paths=None, **kwargs):
        with patch.object(module, 'frozen_blobs', return_value={PATH: 'blob'}):
            with patch.object(module.subprocess, 'check_output', return_value=DATA):
                return module.prepare(repo, snapshot, [PATH] if paths is None else paths, **kwargs)

    def test_collector_body_and_target(self):
        with tempfile.TemporaryDirectory() as folder:
            source, bindings, _ = self.prepare(self.setup_repo(folder))
            anchor = '  let constants := environment.constants.toList.mergeSort '
            self.assertEqual(source[source.index(anchor):], TEMPLATE[TEMPLATE.index(anchor):])
            self.assertIn('import Solidity.Test\n', source)
            self.assertEqual(len(bindings), 1)
            self.assertIn(module.MARKER, source)

    def test_stream_retains_bindings_and_target(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = self.setup_repo(folder)
            sorted_source, sorted_bindings, sorted_template = self.prepare(repo)
            source, bindings, template = self.prepare(repo, stream=True)
            self.assertEqual((bindings, template), (sorted_bindings, sorted_template))
            self.assertIn('import Solidity.Test\n', source)
            self.assertNotIn('constants.toList.mergeSort', source)
            self.assertIn('let constants := environment.constants.toList\n', source)
            self.assertEqual(source.count(module.MARKER), sorted_source.count(module.MARKER))

    def test_result_shape_option_preserves_bindings(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = self.setup_repo(folder)
            ordinary, expected, expected_template = self.prepare(repo, stream=True)
            source, bindings, template = self.prepare(repo, stream=True, result_shapes=True)
            self.assertEqual((bindings, template), (expected, expected_template))
            self.assertIn('("result_shape", resultShape)', source)
            self.assertNotIn('("result_shape", resultShape)', ordinary)
            self.assertEqual(source.count(module.MARKER), ordinary.count(module.MARKER))

    def test_selection_bounds_and_duplicates(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = self.setup_repo(folder)
            for paths in ([], [PATH]*2, ['Solidity/X.lean'], [f'Solidity/T{i}.lean' for i in range(5)]):
                with self.assertRaises(ValueError):
                    self.prepare(repo, paths=paths)

    def test_snapshot_hash_and_duplicate_refuse(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = self.setup_repo(folder)
            for snapshot in ({'modules': SNAPSHOT['modules']*2}, {'modules':[{'file':PATH,'sha256':'wrong'}]}):
                with self.assertRaises(ValueError):
                    self.prepare(repo, snapshot)

    def test_changed_current_import_refuses(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = self.setup_repo(folder)
            (repo/PATH).write_bytes(b'def test := 2')
            with self.assertRaisesRegex(ValueError, 'Current import'):
                self.prepare(repo)

    def test_symlink_current_import_refuses(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = self.setup_repo(folder)
            target = repo/'other.lean'
            target.write_bytes(DATA)
            (repo/PATH).unlink()
            (repo/PATH).symlink_to(target)
            with self.assertRaisesRegex(ValueError, 'Current import'):
                self.prepare(repo)

    def run_main(self, repo, extra=()):
        snapshot = repo/'snapshot.json'
        snapshot.write_text('{}')
        argv = ['generator', '--repo', str(repo), '--snapshot', str(snapshot), '--file', PATH, '--name', 'Safe', *extra]
        with patch.object(sys, 'argv', argv), patch.object(module, 'prepare', return_value=('source', [], 'template')), patch('builtins.print'):
            module.main()

    def test_exclusive_materialization_and_pin(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = self.setup_repo(folder)
            with self.assertRaisesRegex(ValueError, 'hash differs'):
                self.run_main(repo, ('--expect-sha256', 'wrong'))
            self.assertFalse((repo/module.OUTPUT_ROOT).exists())
            self.run_main(repo, ('--expect-sha256', hashlib.sha256(b'source').hexdigest()))
            out = repo/module.OUTPUT_ROOT/'Safe.lean'
            with self.assertRaises(FileExistsError):
                self.run_main(repo)
            self.assertEqual(out.read_text(), 'source')

    def test_bad_name_and_redirected_root(self):
        with tempfile.TemporaryDirectory() as folder:
            repo = self.setup_repo(folder)
            with self.assertRaisesRegex(ValueError, 'filename'):
                self.run_main(repo, ('--name', '../escape'))
            root = repo/module.OUTPUT_ROOT
            root.parent.mkdir(parents=True, exist_ok=True)
            dest = repo/'foreign'
            dest.mkdir()
            root.symlink_to(dest, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, 'escapes'):
                self.run_main(repo)
            self.assertFalse(list(dest.iterdir()))


if __name__ == '__main__':
    unittest.main()
