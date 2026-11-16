"""Guard inherited-byte drift, scope expansion and silent legacy-check bypass."""
import importlib.util
import copy
import json
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

    def test_h309_exact_pair_and_only_one_manifest_leaf_changes(self):
        original = json.loads((gate.ROOT / gate.MANIFEST_PATH).read_text())
        before = copy.deepcopy(original)
        projected, info = gate.runtime_manifest()
        expected = copy.deepcopy(original)
        expected['gate_scripts'][gate.RUNTIME_PATH] = gate.RUNTIME_NEW_SHA256
        self.assertEqual(projected, expected)
        self.assertEqual(original, before)
        self.assertEqual(info['approved_master'], '0781d0b90cfa2773f6304a5da5390eaa7c8c8538')
        self.assertFalse(info['full_acceptance'])
        wrong = copy.deepcopy(original)
        wrong['gate_scripts'][gate.RUNTIME_PATH] = '0' * 64
        with self.assertRaises(ValueError):
            gate.project_runtime_manifest(wrong)
        old = subprocess.check_output(['git', 'show', gate.RUNTIME_OLD_MASTER + ':' + gate.RUNTIME_PATH], cwd=gate.ROOT)
        new = (gate.ROOT / gate.RUNTIME_PATH).read_bytes()
        gate.check_runtime_pair(old, new)
        for a, b in ((old + b'\n', new), (old, new + b'\n')):
            with self.assertRaises(ValueError):
                gate.check_runtime_pair(a, b)

    def test_h309_refuses_modified_numeric_manifest_pins(self):
        path = gate.ROOT / gate.MANIFEST_PATH
        original_read = Path.read_bytes
        manifest = json.loads(original_read(path))
        mutations = []
        source = copy.deepcopy(manifest)
        source['modules'][0]['sha256'] = '0' * 64
        mutations.append(source)
        kernel = copy.deepcopy(manifest)
        kernel['kernel_inventory_sha256'] = '0' * 64
        mutations.append(kernel)
        for mutated in mutations:
            raw = json.dumps(mutated).encode()
            def read(candidate):
                return raw if candidate == path else original_read(candidate)
            with patch.object(Path, 'read_bytes', read):
                with self.assertRaisesRegex(ValueError, 'original acceptance manifest changed'):
                    gate.runtime_manifest()

    def test_h309_configuration_and_serial_mutations_refused(self):
        old = b'moreLeanArgs = ["-j1"]\nnumber = 1\ntargets = ["A"]\n'
        new = b'weakLeanArgs = ["-j1"]\nnumber = 1\ntargets = ["A"]\n'
        gate.serial_runtime_equivalent(old, new)
        for mutation in (new.replace(b'-j1', b'-j2'),
                         new.replace(b'number = 1', b'number = true'),
                         new.replace(b'number = 1', b'number = 1.0'),
                         new.replace(b'["A"]', b'["A", "B"]'),
                         new + b'moreLeanArgs = ["-j1"]\n',
                         new + b'newFlag = true\n'):
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                gate.serial_runtime_equivalent(old, mutation)

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

    def test_overlapping_trees_refused_before_any_staging(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            evidence = base / 'input'
            evidence.mkdir()
            (evidence / 'record.json').write_text('{"source":"unchanged"}')
            alias = base / 'alias'
            alias.symlink_to(evidence, target_is_directory=True)
            before = gate.input_hashes(evidence)
            for output in (evidence / 'output', evidence, base, alias / 'output'):
                with self.subTest(output=output), patch.object(gate, 'git') as git, patch.object(gate.shutil, 'copytree') as copy:
                    with self.assertRaisesRegex(ValueError, 'must not overlap'):
                        gate.stage(evidence, output)
                    git.assert_not_called()
                    copy.assert_not_called()
                self.assertEqual(gate.input_hashes(evidence), before)
                self.assertEqual(set(evidence.iterdir()), {evidence / 'record.json'})
            self.assertFalse((evidence / 'output').exists())

    def test_disjoint_private_trees_still_stage_exact_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            evidence, output = base / 'input', base / 'output'
            evidence.mkdir()
            (evidence / 'record.json').write_text('{}')
            before = gate.input_hashes(evidence)
            with patch.object(gate, 'git', return_value=''):
                snapshot, hashes, sources = gate.stage(evidence, output)
            self.assertEqual(hashes, before)
            self.assertEqual(sources, {})
            self.assertEqual(gate.input_hashes(snapshot / 'tests/sol-numeric-literals/evidence'), before)
            self.assertEqual(gate.input_hashes(evidence), before)

    def test_original_adoption_control_runs_on_exact_frozen_fixture(self):
        original = gate.load_legacy()
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp)
            snapshot = output / 'snapshot'
            for name in (gate.LEGACY, gate.PACKET, 'tests/sol-numeric-literals/test-adoption.py'):
                target = snapshot / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((gate.ROOT / name).read_bytes())
            gate.legacy_adoption_control(original, snapshot, output,
                                         ['python3', 'tests/sol-numeric-literals/test-adoption.py'])
            binding = json.loads((output / 'legacy-adoption-control.json').read_text())
            self.assertTrue(binding['real_checkout_and_index_unchanged'])
            self.assertEqual(binding['published_fixture_master'], original.ADOPTED_MASTER)

    def test_self_tests_require_clean_positive_baseline(self):
        original = types.SimpleNamespace(validate_committed_inputs=Mock(side_effect=ValueError('dirty baseline')))
        with patch.object(gate, 'stage') as stage, patch.object(gate, 'runtime_manifest') as runtime:
            with self.assertRaisesRegex(ValueError, 'dirty baseline'):
                gate.execute(original, Path('/input'), Path('/output'), self_test=True)
            stage.assert_not_called()
            runtime.assert_not_called()
        original.validate_committed_inputs.assert_called_once_with()

    def test_delegation_retains_final_checks_and_redirects_private_io(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            output, evidence = base / 'out', base / 'input'
            output.mkdir(); evidence.mkdir()
            snapshot = output / 'snapshot'
            (snapshot / 'tests/sol-numeric-literals').mkdir(parents=True)
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
                self.assertEqual(json.loads((original.FOLDER / 'acceptance.json').read_text()), {'only': 'private projection'})
                self.assertEqual(original.FOLDER / 'evidence/complete-gates', snapshot / 'tests/sol-numeric-literals/evidence/complete-gates')
                original.run(['python3', 'tests/sol-numeric-literals/differential.py'])
                original.run(['python3', 'tests/sol-numeric-literals/h35/test-h41.py'])
                original.validate_h41_cache_record({})
                raise ValueError('original validation failure')
            original.check = check
            with patch.object(gate, 'stage', return_value=(snapshot, {}, {})), patch.object(gate, 'git', return_value='head'), patch.object(gate, 'runtime_manifest', return_value=({'only': 'private projection'}, {'authority': 'H309'})):
                with self.assertRaisesRegex(ValueError, 'original validation failure'):
                    gate.execute(original, evidence, output)
            self.assertEqual(calls, [['python3', str(snapshot / 'tests/sol-numeric-literals/differential.py')], ['python3', str(snapshot / 'tests/sol-numeric-literals/h35/test-h41.py')], snapshot])
            self.assertIs(original.validate_foreign_paths, foreign)
            self.assertEqual(original.ROOT, gate.ROOT)
            self.assertTrue((output / 'input-binding.json').is_file())


if __name__ == '__main__':
    unittest.main()
