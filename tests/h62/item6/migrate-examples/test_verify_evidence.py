#!/usr/bin/env python3
import copy
import hashlib
import pathlib
import sys
import tempfile
import unittest
ROOT=pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'scripts/h62/item6/migrate-examples'))
import verify_evidence as audit


class EvidenceTests(unittest.TestCase):
    def test_portable_separate_roots_and_tampering(self):
        with tempfile.TemporaryDirectory() as temp:
            root=pathlib.Path(temp);repo=root/'repo';art=root/'extracted'
            repo.mkdir();art.mkdir();(repo/'tool.py').write_bytes(b'code');(art/'capture.log').write_bytes(b'evidence')
            def record(path,anchor):
                return {'path':path.relative_to(anchor).as_posix(),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
            manifest={'schema_version':1,'repository_inputs':[record(repo/'tool.py',repo)],'artifact_files':[record(art/'capture.log',art)]}
            pending=audit.verify(manifest,repo)
            self.assertEqual(pending['status'],'repository_inputs_verified_external_artifacts_pending')
            self.assertIsNone(pending['artifact_files_verified'])
            self.assertEqual(audit.verify(manifest,repo,art)['artifact_files_verified'],1)
            (art/'capture.log').write_bytes(b'tampered')
            with self.assertRaises(ValueError):audit.verify(manifest,repo,art)

    def test_path_escape_duplicate_and_symlink_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            root=pathlib.Path(temp);outside=root/'secret';outside.write_bytes(b'x')
            anchor=root/'anchor';anchor.mkdir();(anchor/'link').symlink_to(outside)
            entry={'path':'link','bytes':1,'sha256':hashlib.sha256(b'x').hexdigest()}
            for path in ('../secret',str(outside),'link'):
                changed=copy.deepcopy(entry);changed['path']=path
                with self.assertRaises(ValueError):audit.verify_files(anchor,[changed])
            (anchor/'real').write_bytes(b'x');entry['path']='real'
            with self.assertRaises(ValueError):audit.verify_files(anchor,[entry,entry])


if __name__=='__main__':unittest.main()
