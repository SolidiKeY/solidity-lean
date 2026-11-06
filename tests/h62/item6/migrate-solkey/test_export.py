#!/usr/bin/env python3
"""Verify evidence bytes survive metadata/head changes deterministically."""
import hashlib
import importlib.util
import os
from pathlib import Path
import tarfile
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[4]
SPEC=importlib.util.spec_from_file_location('export',ROOT/'scripts/h62/item6/migrate-solkey/export.py')
E=importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(E)


class ExportControls(unittest.TestCase):
    def test_deterministic_bytes_and_identity_boundary(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp); evidence=base/'evidence'; evidence.mkdir()
            log=evidence/'result.log'; log.write_text('compiler output\n')
            (evidence/'data.json').write_text('{"exit":0}\n')
            state=evidence/'continuation-state.json'; state.write_text('{"head":"before"}')
            first,second=base/'first.tar.gz',base/'second.tar.gz'
            E.archive_evidence(evidence,first)
            log.chmod(0o600); os.utime(log,(1,1)); state.write_text('{"head":"after"}')
            E.archive_evidence(evidence,second)
            self.assertEqual(hashlib.sha256(first.read_bytes()).hexdigest(),hashlib.sha256(second.read_bytes()).hexdigest())
            with tarfile.open(first) as archive:
                self.assertEqual(archive.getnames(),['data.json','result.log'])
            with self.assertRaises(FileExistsError): E.archive_evidence(evidence,first)


if __name__=='__main__': unittest.main()
