import importlib.util
import json
import pathlib
import re
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[4]
SPEC = importlib.util.spec_from_file_location('collector', ROOT / 'scripts/h62/item1/trust-fragments/collect.py')
COLLECTOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(COLLECTOR)
sys.modules['collect'] = COLLECTOR
ACCEPT_SPEC = importlib.util.spec_from_file_location('accept_baseline', ROOT / 'scripts/h62/item1/trust-fragments/accept_baseline.py')
ACCEPT = importlib.util.module_from_spec(ACCEPT_SPEC)
ACCEPT_SPEC.loader.exec_module(ACCEPT)
sys.modules['accept_baseline'] = ACCEPT
HISTORY_SPEC = importlib.util.spec_from_file_location('lane_history', ROOT / 'scripts/h62/item1/trust-fragments/lane_history.py')
HISTORY = importlib.util.module_from_spec(HISTORY_SPEC)
HISTORY_SPEC.loader.exec_module(HISTORY)
sys.modules['lane_history'] = HISTORY
MIGRATION_SPEC = importlib.util.spec_from_file_location('accept_migration', ROOT / 'scripts/h62/item1/trust-fragments/accept_migration.py')
MIGRATION = importlib.util.module_from_spec(MIGRATION_SPEC)
MIGRATION_SPEC.loader.exec_module(MIGRATION)
CENSUS_SPEC = importlib.util.spec_from_file_location('census', ROOT / 'scripts/h62/item1/trust-fragments/census.py')
CENSUS = importlib.util.module_from_spec(CENSUS_SPEC)
CENSUS_SPEC.loader.exec_module(CENSUS)
sys.modules['census'] = CENSUS
FIXTURE_SPEC = importlib.util.spec_from_file_location('check_fixture', ROOT / 'scripts/h62/item1/trust-fragments/check_fixture.py')
FIXTURE = importlib.util.module_from_spec(FIXTURE_SPEC)
FIXTURE_SPEC.loader.exec_module(FIXTURE)
sys.modules['check_fixture'] = FIXTURE
TIMING_SPEC = importlib.util.spec_from_file_location('time_audit', ROOT / 'scripts/h62/item1/trust-fragments/time_audit.py')
TIMING = importlib.util.module_from_spec(TIMING_SPEC)
TIMING_SPEC.loader.exec_module(TIMING)


class CollectorTests(unittest.TestCase):
    def test_reproduces_frozen_audit(self):
        self.assertEqual(COLLECTOR.collect(COLLECTOR.FRAGMENTS), COLLECTOR.AUDIT.read_bytes())

    def test_migration_acceptance_accounts_for_inputs_and_installed_file(self):
        base = COLLECTOR.AUDIT.read_bytes()
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            lanes = root / 'lanes'
            lane = lanes / 'owner-a'
            lane.mkdir(parents=True)
            (lane / 'extra.json').write_text(json.dumps({
                'imports': ['Solidity.Fixture'],
                'headlines': ['Solidity.Fixture.alpha', 'Solidity.Fixture.beta']}))
            candidate = COLLECTOR.MARKER + COLLECTOR.collect_lanes(base, lanes)
            result = MIGRATION.accept(lanes, candidate)
            with self.assertRaisesRegex(ValueError, 'not installed'):
                MIGRATION.accept(lanes, candidate, require_installed=True)
            self.assertEqual((result['new_imports'], result['new_headlines'], result['checkout_state']), (1, 2, 'original'))
            for altered in [candidate.replace(b'``Solidity.Fixture.alpha', b'``Solidity.Fixture.alphx', 1),
                            candidate.replace(b'import Solidity.Fixture\n', b'', 1),
                            candidate.replace(b'#print axioms ', b'--print axioms ', 1),
                            candidate.replace(b'``propext', b'``propExt', 1)]:
                with self.subTest(altered=altered[:80]), self.assertRaises(ValueError):
                    MIGRATION.accept(lanes, altered)
            with mock.patch.object(COLLECTOR, 'collect_lane_snapshot', return_value=base):
                with self.assertRaisesRegex(ValueError, 'cover exactly'):
                    MIGRATION.accept(lanes)
            bad_patch = root / 'invalid.patch'
            bad_patch.write_text('invalid patch\n')
            with mock.patch.object(MIGRATION, 'PATCH', bad_patch):
                with self.assertRaises(ValueError):
                    MIGRATION.accept(lanes)
            installed = root / 'installed.lean'
            installed.write_bytes(candidate)
            with mock.patch.object(COLLECTOR, 'AUDIT', installed), \
                 mock.patch.object(MIGRATION, 'read_commit_audit', return_value=candidate):
                with self.assertRaisesRegex(ValueError, 'prior commit'):
                    MIGRATION.accept(lanes, require_installed=True)
                with self.assertRaisesRegex(ValueError, 'canonical lane directory'):
                    MIGRATION.accept(lanes, require_installed=True, prior_commit=ACCEPT.BASE)
                tracked = {'owner-a/extra.json': (lane / 'extra.json').read_bytes()}
                with mock.patch.object(COLLECTOR, 'LANES', lanes), \
                     mock.patch.object(HISTORY, 'read_commit_files', return_value=tracked):
                    self.assertEqual(MIGRATION.accept(lanes, require_installed=True, prior_commit=ACCEPT.BASE)['checkout_state'], 'migrated')
                with mock.patch.object(COLLECTOR, 'LANES', lanes), \
                     mock.patch.object(HISTORY, 'read_commit_files', return_value={}):
                    with self.assertRaisesRegex(ValueError, 'committed HEAD'):
                        MIGRATION.accept(lanes, require_installed=True, prior_commit=ACCEPT.BASE)
                with mock.patch.object(COLLECTOR, 'LANES', lanes), \
                     mock.patch.object(HISTORY, 'read_commit_files', return_value=tracked), \
                     mock.patch.object(HISTORY, 'read_current_files', side_effect=[tracked, {}]):
                    with self.assertRaisesRegex(ValueError, 'changed during acceptance'):
                        MIGRATION.accept(lanes, require_installed=True, prior_commit=ACCEPT.BASE)
                self.assertEqual(TIMING.audit_inputs(lanes), (base, candidate))
                installed.write_bytes(candidate + b'-- changed\n')
                with self.assertRaises(ValueError):
                    MIGRATION.accept(lanes)

    def test_snapshot_order_preserves_owner_then_filename_sort(self):
        base = COLLECTOR.AUDIT.read_bytes()
        files = {
            'a-b/z.json': json.dumps({'imports': [], 'headlines': ['Solidity.Fixture.second']}).encode(),
            'a/z.json': json.dumps({'imports': [], 'headlines': ['Solidity.Fixture.first']}).encode()}
        result = COLLECTOR.collect_lane_snapshot(base, files)
        self.assertLess(result.index(b'``Solidity.Fixture.first'), result.index(b'``Solidity.Fixture.second'))
        self.assertEqual(result, COLLECTOR.collect_lane_snapshot(base, dict(reversed(list(files.items())))))

    def test_preservation_uses_one_captured_input_map(self):
        base = COLLECTOR.AUDIT.read_bytes()
        with tempfile.TemporaryDirectory() as tmp:
            lanes = pathlib.Path(tmp) / 'lanes'
            lane = lanes / 'owner-a'
            lane.mkdir(parents=True)
            path = lane / 'extra.json'
            path.write_text(json.dumps({'imports': [], 'headlines': ['Solidity.Fixture.new']}))
            tracked = {'owner-a/extra.json': path.read_bytes()}
            candidate = COLLECTOR.MARKER + COLLECTOR.collect_lanes(base, lanes)
            installed = pathlib.Path(tmp) / 'audit.lean'
            installed.write_bytes(candidate)
            prior = {'owner-a': {'imports': set(), 'headlines': {'Solidity.Fixture.old'}}}
            # Legacy repeated live reads could see old restored just for preservation.
            with mock.patch.object(COLLECTOR, 'AUDIT', installed), \
                 mock.patch.object(COLLECTOR, 'LANES', lanes), \
                 mock.patch.object(HISTORY, 'read_commit_files', return_value=tracked), \
                 mock.patch.object(HISTORY, 'read_commit', return_value=prior), \
                 mock.patch.object(HISTORY, 'read_current', return_value=prior), \
                 mock.patch.object(MIGRATION, 'read_commit_audit', return_value=candidate):
                with self.assertRaisesRegex(ValueError, 'removed or reassigned'):
                    MIGRATION.accept(lanes, require_installed=True, prior_commit='1'*40)

    def test_acceptance_rechecks_raw_fragments_and_lane_entry_types(self):
        base = COLLECTOR.AUDIT.read_bytes()
        with tempfile.TemporaryDirectory() as tmp:
            lanes = pathlib.Path(tmp) / 'lanes'
            with mock.patch.object(COLLECTOR, 'collect', side_effect=[base, base+b'changed']):
                with self.assertRaisesRegex(ValueError, 'raw fragments changed'):
                    MIGRATION.accept(lanes)
            lane = lanes / 'owner-a'
            lane.mkdir(parents=True)
            path = lane / 'extra.json'
            path.write_text(json.dumps({'imports': [], 'headlines': ['Solidity.Fixture.new']}))
            other = pathlib.Path(tmp) / 'same.json'
            other.write_bytes(path.read_bytes())
            real_coverage = MIGRATION.coverage
            def swap(*args):
                result = real_coverage(*args)
                path.unlink()
                path.symlink_to(other)
                return result
            with mock.patch.object(MIGRATION, 'coverage', side_effect=swap):
                with self.assertRaisesRegex(ValueError, 'invalid lane fragment'):
                    MIGRATION.accept(lanes)

    def test_installed_gate_requires_committed_audit(self):
        base = COLLECTOR.AUDIT.read_bytes()
        with tempfile.TemporaryDirectory() as tmp:
            lanes = pathlib.Path(tmp) / 'lanes'
            installed = pathlib.Path(tmp) / 'audit.lean'
            installed.write_bytes(COLLECTOR.MARKER + base)
            with mock.patch.object(COLLECTOR, 'AUDIT', installed), \
                 mock.patch.object(COLLECTOR, 'LANES', lanes), \
                 mock.patch.object(HISTORY, 'read_commit_files', return_value={}), \
                 mock.patch.object(MIGRATION, 'read_commit_audit', return_value=base):
                with self.assertRaisesRegex(ValueError, 'audit does not match committed HEAD'):
                    MIGRATION.accept(lanes, require_installed=True, prior_commit=ACCEPT.BASE)

    def test_resource_limit_and_process_group_abort(self):
        with mock.patch.object(FIXTURE.resource, 'setrlimit') as setlimit:
            FIXTURE.limit_memory()
            setlimit.assert_called_once_with(FIXTURE.resource.RLIMIT_AS, (8*1024**3, 8*1024**3))
        process = mock.Mock(pid=12345)
        process.communicate.side_effect = [subprocess.TimeoutExpired('fake', .25), ('', None)]
        with mock.patch.object(FIXTURE, 'headroom'), \
             mock.patch.object(FIXTURE.subprocess, 'Popen', return_value=process) as launch, \
             mock.patch.object(FIXTURE.time, 'monotonic', side_effect=[0, 2]), \
             mock.patch.object(FIXTURE.os, 'killpg') as kill:
            with self.assertRaises(TimeoutError):
                FIXTURE.run_bounded(['fake'], ROOT, {}, 1)
            self.assertTrue(launch.call_args.kwargs['start_new_session'])
            kill.assert_called_once_with(12345, FIXTURE.signal.SIGKILL)
            self.assertEqual(process.communicate.call_count, 2)
        process = mock.Mock(pid=12346)
        process.communicate.side_effect = [subprocess.TimeoutExpired('fake', .25), ('', None)]
        with mock.patch.object(FIXTURE, 'headroom', side_effect=[None, RuntimeError('reserve crossed')]), \
             mock.patch.object(FIXTURE.subprocess, 'Popen', return_value=process), \
             mock.patch.object(FIXTURE.os, 'killpg') as kill:
            with self.assertRaisesRegex(RuntimeError, 'reserve crossed'):
                FIXTURE.run_bounded(['fake'], ROOT, {}, 1)
            kill.assert_called_once_with(12346, FIXTURE.signal.SIGKILL)
            self.assertEqual(process.communicate.call_count, 2)

    def test_fixture_rejects_unpinned_toolchain(self):
        with self.assertRaisesRegex(ValueError, 'toolchain paths'):
            FIXTURE.pinned_tools(pathlib.Path('/tmp/other/lean'), pathlib.Path('/tmp/archive.tar.zst'))
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            archive = root / 'lean-4.35.0-linux.tar.zst'
            archive.write_bytes(b'not the official archive')
            with self.assertRaisesRegex(ValueError, 'archive checksum mismatch'):
                FIXTURE.pinned_tools(root/'lean-4.35.0-linux/bin/lean', archive)

    def test_prior_lane_entries_cannot_disappear_or_change_owner(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            lane = root / 'owner-a'
            lane.mkdir()
            data = {'imports': ['Solidity.Fixture'], 'headlines': ['Solidity.Fixture.alpha']}
            (lane / 'one.json').write_text(json.dumps(data))
            prior = {'owner-a': {'imports': {'Solidity.Fixture'}, 'headlines': {'Solidity.Fixture.alpha'}}}
            self.assertEqual(HISTORY.read_current(root), prior)
            HISTORY.preserve(prior, HISTORY.read_current(root))
            with mock.patch.object(HISTORY, 'read_commit', return_value=prior):
                self.assertEqual(MIGRATION.accept(root, prior_commit='1' * 40)['prior_commit'], '1' * 40)
                (lane / 'one.json').unlink()
                lane.rmdir()
                with self.assertRaisesRegex(ValueError, 'removed or reassigned'):
                    MIGRATION.accept(root, prior_commit='1' * 40)
                other = root / 'owner-b'
                other.mkdir()
                (other / 'one.json').write_text(json.dumps(data))
                with self.assertRaisesRegex(ValueError, 'removed or reassigned'):
                    MIGRATION.accept(root, prior_commit='1' * 40)
        with self.assertRaises(ValueError):
            HISTORY.read_commit('master')
        self.assertEqual(HISTORY.read_commit(ACCEPT.BASE), {})
        self.assertEqual(HISTORY.read_commit_files(ACCEPT.BASE), {})

    def test_prior_commit_tree_is_read_and_symlinks_rejected(self):
        commit = '1' * 40
        blob = '2' * 40
        path = 'tests/h62/item1/trust-fragments/lanes/owner-a/one.json'
        data = json.dumps({'imports': ['Solidity.Fixture'], 'headlines': ['Solidity.Fixture.alpha']}).encode()
        def output(args, **kwargs):
            if args[1:3] == ['cat-file', '-t']:
                return b'commit\n'
            if args[1] == 'ls-tree':
                if args[-1] != HISTORY.LANE_ROOT:
                    raise AssertionError('lane root must be included in pathspec')
                return f'100644 blob {blob}\t{path}\0'.encode()
            if args[1:3] == ['cat-file', 'blob']:
                return data
            raise AssertionError(args)
        with mock.patch.object(HISTORY.subprocess, 'check_output', side_effect=output), \
             mock.patch.object(HISTORY.subprocess, 'run', return_value=mock.Mock(returncode=0)):
            prior = HISTORY.read_commit(commit)
            self.assertEqual(prior['owner-a']['headlines'], {'Solidity.Fixture.alpha'})
        def bad_mode(args, **kwargs):
            value = output(args, **kwargs)
            return value.replace(b'100644 blob', b'120000 blob') if args[1] == 'ls-tree' else value
        with mock.patch.object(HISTORY.subprocess, 'check_output', side_effect=bad_mode), \
             mock.patch.object(HISTORY.subprocess, 'run', return_value=mock.Mock(returncode=0)):
            with self.assertRaisesRegex(ValueError, 'invalid committed lane entry'):
                HISTORY.read_commit(commit)
        def root_symlink(args, **kwargs):
            value = output(args, **kwargs)
            return f'120000 blob {blob}\t{HISTORY.LANE_ROOT}\0'.encode() if args[1] == 'ls-tree' else value
        with mock.patch.object(HISTORY.subprocess, 'check_output', side_effect=root_symlink), \
             mock.patch.object(HISTORY.subprocess, 'run', return_value=mock.Mock(returncode=0)):
            with self.assertRaisesRegex(ValueError, 'invalid committed lane entry'):
                HISTORY.read_commit(commit)
        def root_gitlink(args, **kwargs):
            value = output(args, **kwargs)
            return f'160000 commit {blob}\t{HISTORY.LANE_ROOT}\0'.encode() if args[1] == 'ls-tree' else value
        with mock.patch.object(HISTORY.subprocess, 'check_output', side_effect=root_gitlink), \
             mock.patch.object(HISTORY.subprocess, 'run', return_value=mock.Mock(returncode=0)):
            with self.assertRaisesRegex(ValueError, 'invalid committed lane entry'):
                HISTORY.read_commit(commit)
        with mock.patch.object(HISTORY.subprocess, 'check_output', side_effect=output), \
             mock.patch.object(HISTORY.subprocess, 'run', return_value=mock.Mock(returncode=1)):
            with self.assertRaisesRegex(ValueError, 'ancestor'):
                HISTORY.read_commit(commit)
        inventory = {}
        HISTORY.add(inventory, 'owner-a', data.decode())
        with self.assertRaisesRegex(ValueError, 'duplicate committed headline'):
            HISTORY.add(inventory, 'owner-b', data.decode())

    def test_real_git_tree_rejects_uncommitted_audit(self):
        if COLLECTOR.LANES.exists():
            self.skipTest('fixture assumes no real lane fragments')
        base = COLLECTOR.AUDIT.read_bytes()
        self.assertEqual(base, COLLECTOR.collect(COLLECTOR.FRAGMENTS))
        with tempfile.TemporaryDirectory() as directory:
            installed = pathlib.Path(directory) / 'TrustAudit.lean'
            installed.write_bytes(COLLECTOR.MARKER + base)
            with mock.patch.object(COLLECTOR, 'AUDIT', installed):
                with self.assertRaisesRegex(ValueError, 'installed audit does not match committed HEAD'):
                    MIGRATION.accept(COLLECTOR.LANES, require_installed=True, prior_commit=ACCEPT.BASE)
                result = MIGRATION.accept(COLLECTOR.LANES, prior_commit=ACCEPT.BASE)
        self.assertEqual(result['checkout_state'], 'migrated')
        self.assertEqual(result['new_headlines'], 0)
        self.assertEqual(COLLECTOR.AUDIT.read_bytes(), base)

    def test_fragment_symlinks_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / '000-a.leanfrag').symlink_to(COLLECTOR.AUDIT)
            with self.assertRaises(ValueError):
                COLLECTOR.collect(root)
            link = root.parent / (root.name + '-link')
            link.symlink_to(root)
            try:
                with self.assertRaises(ValueError):
                    COLLECTOR.collect(link)
            finally:
                link.unlink()

    def test_independent_lane_additions_preserve_baseline(self):
        base = COLLECTOR.AUDIT.read_bytes()
        with tempfile.TemporaryDirectory() as directory:
            lanes = pathlib.Path(directory)
            for lane, headline in [('lane-b', 'Solidity.Fixture.b'), ('lane-a', 'Solidity.Fixture.a')]:
                path = lanes / lane
                path.mkdir()
                (path / 'checks.json').write_text(json.dumps({
                    'imports': ['Solidity.Fixture', 'Solidity.Theorems'], 'headlines': [headline]}))
            result = COLLECTOR.collect_lanes(base, lanes)
            self.assertTrue(result.startswith(b'import Solidity.Fixture\n'))
            additions = b',\n    ``Solidity.Fixture.a,\n    ``Solidity.Fixture.b'
            self.assertEqual(result.count(additions), 1)
            self.assertEqual(result.replace(b'import Solidity.Fixture\n', b'', 1).replace(additions, b'', 1), base)
            self.assertEqual(result.count(b'  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]'), 44)
            original, candidate = TIMING.audit_inputs(lanes)
            self.assertEqual(original, base)
            self.assertEqual(candidate, COLLECTOR.MARKER + result)

    def test_lane_inputs_fail_closed(self):
        base = COLLECTOR.AUDIT.read_bytes()
        with tempfile.TemporaryDirectory() as directory:
            lanes = pathlib.Path(directory)
            lane = lanes / 'lane-a'
            lane.mkdir()
            path = lane / 'checks.json'
            for payload in [
                {'imports': [], 'headlines': []},
                {'imports': ['Lean.Bad'], 'headlines': ['Solidity.Fixture.a']},
                {'imports': [], 'headlines': ['Solidity.Fixture.a\n#eval 1']},
                {'imports': [], 'headlines': ['Solidity.MemoryWitness.bind_exact']},
                {'imports': [], 'headlines': ['Solidity.Fixture.a', 'Solidity.Fixture.a']},
                {'imports': [], 'headlines': ['Solidity.Fixture.a'], 'extra': True},
            ]:
                path.write_text(json.dumps(payload))
                with self.subTest(payload=payload), self.assertRaises(ValueError):
                    COLLECTOR.collect_lanes(base, lanes)
            path.write_text('{"imports": [], "headlines": ["Solidity.Fixture.a"], "headlines": ["Solidity.Fixture.b"]}')
            with self.assertRaises(ValueError):
                COLLECTOR.collect_lanes(base, lanes)
            path.write_text(json.dumps({'imports': [], 'headlines': ['Solidity.Fixture.a']}))
            with self.assertRaises(ValueError):
                COLLECTOR.collect_lanes(base + b'-- changed', lanes)
            path.unlink()
            path.symlink_to(COLLECTOR.AUDIT)
            with self.assertRaises(ValueError):
                COLLECTOR.collect_lanes(base, lanes)

    def test_timing_gate_boundary(self):
        self.assertFalse(TIMING.is_slow(100.0, 110.0))
        self.assertTrue(TIMING.is_slow(100.0, 110.001))
        with self.assertRaises(ValueError):
            TIMING.is_slow(0, 1)

    def test_census_accounts_for_each_original_occurrence(self):
        data = COLLECTOR.AUDIT.read_bytes()
        inventory = CENSUS.census(data)
        blocks = inventory['audit_blocks']
        names = [name for block in blocks for name in block['headlines']]
        self.assertEqual(len(blocks), 44)
        self.assertEqual(len(names), 1380)
        self.assertEqual(len(set(names)), 1373)
        self.assertEqual(len(inventory['imports']), 77)
        self.assertEqual(len(inventory['print_axioms']), 17)
        self.assertEqual(CENSUS.census(COLLECTOR.collect(COLLECTOR.FRAGMENTS)), inventory)
        with self.assertRaises(ValueError):
            CENSUS.census(data.replace(b'``Solidity.', b'``solidity.', 1))

    def test_pinned_acceptance_detects_matching_mutations(self):
        original = COLLECTOR.AUDIT.read_bytes()
        ACCEPT.accept(original, original, original)
        mutated = original.replace(b'``propext', b'``propExt', 1)
        self.assertNotEqual(mutated, original)
        with self.assertRaises(ValueError):
            ACCEPT.accept(mutated, mutated, mutated)
        with self.assertRaises(ValueError):
            ACCEPT.accept(original, mutated, original)
        with self.assertRaises(ValueError):
            ACCEPT.accept(original, original, mutated)
        with self.assertRaises(ValueError):
            ACCEPT.accept(original, original.replace(b'#print axioms ', b'--print axioms ', 1), original)

    def test_missing_and_unexpected_fragments_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory)
            (path / '000-a.leanfrag').write_bytes(b'a')
            (path / '002-c.leanfrag').write_bytes(b'c')
            with self.assertRaises(ValueError):
                COLLECTOR.collect(path)
            (path / '002-c.leanfrag').unlink()
            (path / 'unexpected').write_bytes(b'x')
            with self.assertRaises(ValueError):
                COLLECTOR.collect(path)

    def test_baseline_census(self):
        data = COLLECTOR.collect(COLLECTOR.FRAGMENTS)
        self.assertEqual(len(re.findall(rb'^run_cmd do$', data, re.M)), 44)
        allowed = rb'^  let allowed : List Name := \[``propext, ``Classical.choice, ``Quot.sound\]$'
        self.assertEqual(len(re.findall(allowed, data, re.M)), 44)
        self.assertEqual(len(re.findall(rb'^#print axioms ', data, re.M)), 17)
        self.assertEqual(len(re.findall(rb'``Solidity\.', data)), 1380)
        for fragment in COLLECTOR.FRAGMENTS.iterdir():
            self.assertEqual(len(re.findall(rb'^run_cmd do$', fragment.read_bytes(), re.M)), 1)

    def test_migration_patch_matches_generated_output(self):
        patch = ROOT / 'scripts/h62/item1/trust-fragments/migration.patch'
        with tempfile.TemporaryDirectory() as directory:
            output = pathlib.Path(directory) / 'TrustAudit.lean'
            result = subprocess.run(['patch', '--silent', '--output', str(output),
                                     str(COLLECTOR.AUDIT), str(patch)], capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(output.read_bytes(), COLLECTOR.MARKER + COLLECTOR.collect(COLLECTOR.FRAGMENTS))

    def test_check_rejects_mutation_and_missing_last_fragment(self):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory)
            for fragment in COLLECTOR.FRAGMENTS.iterdir():
                (path / fragment.name).write_bytes(fragment.read_bytes())
            files = sorted(path.iterdir())
            files[-1].unlink()
            result = subprocess.run([sys.executable, str(ROOT / 'scripts/h62/item1/trust-fragments/collect.py'),
                                     '--fragments', str(path)], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            files[-1].write_bytes(b'changed')
            result = subprocess.run([sys.executable, str(ROOT / 'scripts/h62/item1/trust-fragments/collect.py'),
                                     '--fragments', str(path)], capture_output=True)
            self.assertNotEqual(result.returncode, 0)

    def test_order_and_byte_preservation(self):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory)
            (path / '001-b.leanfrag').write_bytes(b'\x00b\n')
            (path / '000-a.leanfrag').write_bytes(b'a\r\n')
            self.assertEqual(COLLECTOR.collect(path), b'a\r\n\x00b\n')


if __name__ == '__main__':
    unittest.main()
