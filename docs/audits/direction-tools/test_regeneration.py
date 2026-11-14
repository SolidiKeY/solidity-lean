#!/usr/bin/env python3
"""Orchestration controls and a real pinned-producer integration run."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import sys
import unittest

SCRIPT = Path(__file__).with_name('check-regeneration.py')
spec = importlib.util.spec_from_file_location('regeneration', SCRIPT)
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)

class Controls(unittest.TestCase):
    def rejected(self, function, *args):
        with self.assertRaises(r.VerificationError):
            function(*args)

    def test_manifest(self):
        inventory = [('a', 'oid', 2), ('b', 'oid2', 1)]
        r.validate_manifest(inventory, ['a', 'b'], 2, 3)
        self.rejected(r.validate_manifest, inventory, ['a'], 2, 3)
        self.rejected(r.validate_manifest, inventory, ['a', 'a'], 2, 3)
        self.rejected(r.validate_manifest, inventory[:1], ['a'], 2, 3)
        self.rejected(r.validate_manifest, inventory + [inventory[0]], ['a', 'b'], 3, 5)

    def test_comparison(self):
        expected = [('a', b'12'), ('b', b'3')]
        r.compare(expected, expected)
        for actual in ([('a', b'12')], [('a', b'13'), ('b', b'3')],
                       [('wrong', b'12'), ('b', b'3')], expected + [('extra', b'4')],
                       expected + [('a', b'12')]):
            self.rejected(r.compare, expected, actual)

    def test_discovery_and_rename_deletion(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'wrong').mkdir()
            (root / 'wrong/modules-00.json').write_bytes(b'x')
            found = r.discover(root)
            self.rejected(r.compare, [('census/modules-00.json', b'x')], found)
            def git(*args):
                subprocess.run(['git', '-C', tmp, *args], check=True, stdout=subprocess.DEVNULL)
            git('init', '-q')
            git('config', 'user.name', 'Control')
            git('config', 'user.email', 'control@example.invalid')
            (root / 'retained').write_bytes(b'preserve')
            git('add', 'retained')
            git('commit', '-qm', 'base')
            (root / 'retained').write_bytes(b'altered')
            git('add', 'retained')
            (root / 'retained').write_bytes(b'preserve')
            self.rejected(r.verify_retained, [('retained', b'preserve')], r.index_files(root, ['retained']))
            git('reset', '-q', 'HEAD', '--', 'retained')
            git('mv', 'retained', 'renamed')
            self.assertEqual(r.deletions(root, 'HEAD'), ['retained'])
            shard = root / 'docs/audits/direction-tools/census/modules-00.json'
            shard.parent.mkdir(parents=True)
            shard.write_bytes(b'x')
            misplaced = root / 'docs/audits/direction-tools/wrong/modules-01.json'
            misplaced.parent.mkdir(parents=True)
            misplaced.write_bytes(b'x')
            relocated = root / 'docs/audit-copy/modules-00.json'
            relocated.parent.mkdir(parents=True)
            relocated.write_bytes(b'historical shard bytes')
            unrelated = root / 'docs/unrelated/modules-00.json'
            unrelated.parent.mkdir(parents=True)
            unrelated.write_bytes(b'unrelated bytes')
            git('add', str(shard.relative_to(root)), str(misplaced.relative_to(root)), str(relocated.relative_to(root)), str(unrelated.relative_to(root)))
            oid = subprocess.check_output(['git', '-C', tmp, 'rev-parse', ':' + str(relocated.relative_to(root))], text=True).strip()
            historical = {oid: b'historical shard bytes'}
            self.assertEqual(set(r.tracked_shards(root, historical)), {str(p.relative_to(root)) for p in (shard, misplaced, relocated)})
            self.rejected(r.reject_tracked, r.tracked_shards(root, historical))
            git('rm', '--cached', '-q', str(shard.relative_to(root)), str(misplaced.relative_to(root)))
            self.assertEqual(r.tracked_shards(root, historical), [str(relocated.relative_to(root))])
            self.rejected(r.reject_tracked, r.tracked_shards(root, historical))
            git('rm', '--cached', '-q', str(relocated.relative_to(root)))
            renamed = root / 'docs/audit-copy/payload.json'
            renamed.write_bytes(b'historical shard bytes')
            git('add', str(renamed.relative_to(root)))
            oid = subprocess.check_output(['git', '-C', tmp, 'rev-parse', ':' + str(renamed.relative_to(root))], text=True).strip()
            self.assertEqual(r.tracked_shards(root), [])
            self.assertEqual(r.tracked_shards(root, {oid: b'historical shard bytes'}), [str(renamed.relative_to(root))])
            self.rejected(r.reject_tracked, r.tracked_shards(root, {oid: b'historical shard bytes'}))
            git('rm', '--cached', '-q', str(renamed.relative_to(root)))
            self.assertEqual(r.tracked_shards(root, historical), [])
            r.reject_tracked(r.tracked_shards(root, historical))

    def test_retained(self):
        retained = [('script', b'x'), ('summary', b'y')]
        r.verify_retained(retained, retained)
        self.rejected(r.verify_retained, retained, retained[:1])
        self.rejected(r.verify_retained, retained, [('script', b'z'), retained[1]])

    def test_tracked(self):
        r.reject_tracked([])
        self.rejected(r.reject_tracked, ['census/modules-00.json'])

    def test_real_regeneration(self):
        subprocess.run([sys.executable, '-B', str(SCRIPT), '--check'], check=True)

if __name__ == '__main__':
    unittest.main()
