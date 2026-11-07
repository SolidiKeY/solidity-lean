"""Guard portable source tests versus mandatory hash-verified external evidence."""
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'scripts/h62/item2/audit-v09-passes'))
import selected_heap_artifacts as artifacts

class ArtifactBoundary(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.manifest = self.root/'manifest.json'
        self.entry = dict(repository_path='tests/proof.lean',path='proof.lean',bytes=4,
                          sha256=hashlib.sha256(b'good').hexdigest())
        self.manifest.write_text(json.dumps({'files':[self.entry]}))
        self.addCleanup(patch.stopall)
        patch.object(artifacts,'MANIFEST',self.manifest).start()
        patch.dict(os.environ,{'VY3_AUDIT_ARTIFACTS':str(self.root)}).start()

    def test_staged_bytes_are_verified(self):
        (self.root/'proof.lean').write_bytes(b'good')
        self.assertEqual(artifacts.artifact('proof.lean')[1],b'good')

    def test_missing_and_changed_bytes_are_errors(self):
        with self.assertRaises(FileNotFoundError): artifacts.artifact('proof.lean')
        (self.root/'proof.lean').write_bytes(b'evil')
        with self.assertRaises(ValueError): artifacts.artifact('proof.lean')

    def test_manifest_cannot_escape_staging_root(self):
        for path in ['../escape.lean','/absolute.lean']:
            self.entry['path']=path
            self.manifest.write_text(json.dumps({'files':[self.entry]}))
            with self.assertRaises(ValueError): artifacts.artifact('proof.lean')

    def test_materialize_preserves_different_work(self):
        with patch.object(artifacts,'ROOT',self.root):
            target=self.root/'tests/proof.lean'
            target.parent.mkdir()
            target.write_bytes(b'work')
            with self.assertRaises(ValueError): artifacts.materialize(self.entry,b'good')
            self.assertEqual(target.read_bytes(),b'work')
