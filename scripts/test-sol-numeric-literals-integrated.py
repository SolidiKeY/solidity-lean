"""Guard inherited-byte drift, scope expansion and silent legacy-check bypass."""
import importlib.util
from pathlib import Path
import tempfile
import os
import subprocess
import types
import unittest
from unittest.mock import Mock, patch

spec = importlib.util.spec_from_file_location('integrated', Path(__file__).with_name('check-sol-numeric-literals-integrated.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class IntegratedTests(unittest.TestCase):
    def test_only_exact_control_files_extend_local_scope(self):
        original = types.SimpleNamespace(permitted=lambda p: p.startswith('Solidity/Frontend/NumericLiteralProofs/'))
        self.assertTrue(gate.permitted(original, 'Solidity/Frontend/NumericLiteralProofs/X.lean'))
        for path in gate.CONTROL_FILES:
            self.assertTrue(gate.permitted(original, path))
        for path in ['Solidity/Source/Types.lean', 'scripts/other.py',
                     'scripts/check-sol-numeric-literals-integrated.py.extra']:
            self.assertFalse(gate.permitted(original, path))

    def test_foreign_guard_refuses_drift_and_untracked_bytes(self):
        with patch.object(gate.subprocess, 'run', return_value=types.SimpleNamespace(returncode=0)) as run:
            gate.foreign_guard(['Solidity.lean'], set())
            self.assertEqual(run.call_args.args[0], ['git', 'diff', '--quiet', gate.APPROVED_MASTER, '--', 'Solidity.lean'])
            with self.assertRaises(ValueError):
                gate.foreign_guard(['foreign'], {'foreign'})
        with patch.object(gate.subprocess, 'run', return_value=types.SimpleNamespace(returncode=1)):
            with self.assertRaises(ValueError):
                gate.foreign_guard(['Solidity.lean'], set())

    def test_scope_precheck_has_no_coordinator_root_bypass(self):
        original = types.SimpleNamespace(permitted=lambda p: False, changed_paths=lambda tree=None: {'Solidity.lean'})
        git = lambda *args: gate.BRANCH if args[0] == 'branch' else ''
        with patch.object(gate, 'git', side_effect=git), patch.object(gate.subprocess, 'run'), patch.object(gate, 'foreign_guard', side_effect=ValueError('drift')):
            with self.assertRaises(ValueError):
                gate.scope(original)
        with patch.object(gate, 'git', return_value='wrong'):
            with self.assertRaises(ValueError):
                gate.scope(original)

    def test_legacy_sources_remain_exact_and_guard_fails_independently(self):
        original = gate.load_legacy()
        # This current documentation is inherited from the H296 master but is
        # deliberately different from the old adopted publication.
        with self.assertRaises(ValueError):
            original.validate_foreign_paths(['docs/contributing.md'], set())

    def test_new_master_deletion_and_reversion_cannot_disappear(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            def git(*args):
                return subprocess.check_output(['git', *args], cwd=root, text=True).strip()
            git('init', '-q')
            (root / 'Old.txt').write_text('old')
            git('add', '.')
            git('-c', 'user.name=test', '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'base')
            base = git('rev-parse', 'HEAD')
            (root / 'Old.txt').write_text('new')
            (root / 'New.txt').write_text('introduced')
            git('add', '.')
            git('-c', 'user.name=test', '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'approved')
            approved = git('rev-parse', 'HEAD')
            (root / 'New.txt').unlink()
            (root / 'Old.txt').write_text('old')
            legacy = lambda tree=None: set(git('diff', '--name-only', base, *([tree] if tree else []), '--').splitlines())
            self.assertEqual(legacy(), set())
            with patch.object(gate, 'ROOT', root), patch.object(gate, 'APPROVED_MASTER', approved):
                for tree in (None, base):
                    found = gate.changed_paths(legacy, tree)
                    self.assertEqual(found, {'New.txt', 'Old.txt'})
                    with self.assertRaises(ValueError):
                        gate.foreign_guard(found, set(), tree)

    def test_folder_retains_real_path_for_uncommitted_input_control(self):
        with tempfile.TemporaryDirectory() as tmp:
            folder = gate.Folder(Path(tmp), Path(tmp) / 'private')
            fd, name = tempfile.mkstemp(dir=folder)
            os.close(fd)
            self.assertEqual(Path(name).parent, Path(tmp))
            Path(name).unlink()

    def test_private_inputs_refuse_symlinks_and_checkout_paths(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'record').write_text('{}')
            self.assertEqual(set(gate.input_hashes(root)), {'record'})
            (root / 'alias').symlink_to(root / 'record')
            with self.assertRaises(ValueError):
                gate.input_hashes(root)
            with self.assertRaises(ValueError):
                gate.stage(root, gate.ROOT / 'not-an-output')

    def test_delegation_retains_final_checks_and_redirects_private_io(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            output, evidence = base / 'out', base / 'input'
            output.mkdir(); evidence.mkdir()
            snapshot = output / 'snapshot'
            calls = []
            original = types.SimpleNamespace(FOLDER=gate.ROOT / 'tests/sol-numeric-literals',
                ROOT=gate.ROOT, run=lambda c: calls.append(c), permitted=lambda p: False,
                validate_foreign_paths=object(), validate_h41_cache_record=lambda r: calls.append(original.ROOT),
                changed_paths=lambda tree=None: set(),
                validate_completion=object(), validate_inventory=object(), validate_registration=object())
            unchanged = (original.validate_completion, original.validate_inventory, original.validate_registration)
            foreign = original.validate_foreign_paths
            def check(implementation, self_test):
                self.assertEqual((implementation, self_test), (False, False))
                self.assertEqual(unchanged, (original.validate_completion, original.validate_inventory, original.validate_registration))
                self.assertEqual(original.FOLDER / 'evidence/complete-gates', snapshot / 'tests/sol-numeric-literals/evidence/complete-gates')
                original.run(['python3', 'tests/sol-numeric-literals/differential.py'])
                original.validate_h41_cache_record({})
                raise ValueError('original validation failure')
            original.check = check
            with patch.object(gate, 'stage', return_value=(snapshot, {}, {})), patch.object(gate, 'git', return_value='head'):
                with self.assertRaisesRegex(ValueError, 'original validation failure'):
                    gate.execute(original, evidence, output)
            self.assertEqual(calls, [['python3', str(snapshot / 'tests/sol-numeric-literals/differential.py')], snapshot])
            self.assertIs(original.validate_foreign_paths, foreign)
            self.assertEqual(original.ROOT, gate.ROOT)
            self.assertTrue((output / 'input-binding.json').is_file())


if __name__ == '__main__':
    unittest.main()
