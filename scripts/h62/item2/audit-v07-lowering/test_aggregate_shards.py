"""Prevent duplicate, missing, unknown or drifted modules inflating coverage."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from aggregate_elaborated_shards import partition


class PartitionGuards(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo=Path(self.temp.name)/'repo'
        (self.repo/'Example').mkdir(parents=True)
        self.a=self.repo/'Example/A.lean';self.a.write_bytes(b'frozen A')
        self.b=self.repo/'Example/B.lean';self.b.write_bytes(b'current B')
        sha=lambda b:hashlib.sha256(b).hexdigest()
        self.ledger=dict(modules=[dict(path='Example/A.lean',sha256=sha(b'frozen A'),candidate_count=2),dict(path='Example/B.lean',sha256=sha(b'frozen B'),candidate_count=3)])
        self.folder=Path(self.temp.name)/'shard';self.folder.mkdir()
        (self.folder/'pins.json').write_text(json.dumps(dict(modules=['Example.A'])))
        self.plan=[dict(folder=str(self.folder))]

    def test_exact_partition(self):
        selected,drifted=partition(self.repo,self.ledger,self.plan)
        self.assertEqual(selected,{'Example.A'})
        self.assertEqual([r['path'] for r in drifted],['Example/B.lean'])
        self.assertEqual(drifted[0]['source_candidate_count'],3)

    def test_duplicate(self):
        with self.assertRaisesRegex(ValueError,'duplicate selected'):
            partition(self.repo,self.ledger,self.plan+self.plan)

    def test_missing(self):
        with self.assertRaisesRegex(ValueError,'coverage mismatch'):
            partition(self.repo,self.ledger,[])

    def test_unknown(self):
        (self.folder/'pins.json').write_text(json.dumps(dict(modules=['Example.Unknown'])))
        with self.assertRaisesRegex(ValueError,'unknown'):
            partition(self.repo,self.ledger,self.plan)

    def test_new_drift_not_silently_credited(self):
        self.a.write_bytes(b'changed A')
        with self.assertRaisesRegex(ValueError,'coverage mismatch'):
            partition(self.repo,self.ledger,self.plan)


if __name__ == '__main__':
    unittest.main()
