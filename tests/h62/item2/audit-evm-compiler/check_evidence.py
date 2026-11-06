#!/usr/bin/env python3
"""Meaningful corruption controls for portable artifact verification."""
import hashlib,importlib.util,json,pathlib,tarfile,tempfile,unittest
ROOT=pathlib.Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('verify_evidence',ROOT/'scripts/h62/item2/audit-evm-compiler/verify_evidence.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
class EvidenceControls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.root=pathlib.Path(self.tmp.name)
        self.repo=self.root/'repo';self.repo.mkdir();self.data=self.root/'data';self.data.mkdir()
        (self.repo/'source.py').write_bytes(b'checker source');(self.data/'result.json').write_bytes(b'checked result')
        sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
        self.doc=dict(schema_version=1,archive_root='evidence',sources=[dict(path='source.py',sha256=sha(self.repo/'source.py'))],artifacts=[dict(path='result.json',sha256=sha(self.data/'result.json'))])
        self.manifest=self.root/'manifest.json';self.save()
    def save(self):self.manifest.write_text(json.dumps(self.doc))
    def archive(self,duplicate=False):
        p=self.root/'evidence.tar'
        with tarfile.open(p,'w') as t:
            t.add(self.data/'result.json',arcname='evidence/result.json')
            if duplicate:t.add(self.data/'result.json',arcname='evidence/result.json')
        return p
    def test_directory_and_archive(self):
        for kwargs in [dict(artifact_root=self.data),dict(archive=self.archive())]:
            self.assertEqual(v.verify(self.manifest,repo_root=self.repo,**kwargs)['artifacts_verified'],1)
    def test_repository_sources_without_vm_artifacts(self):
        (self.data/'result.json').unlink()
        result=v.verify(self.manifest,repo_root=self.repo,sources_only=True)
        self.assertEqual(result,dict(sources_verified=1,artifacts_verified=0,status='source-pins-pass'))
    def test_artifact_corruption(self):
        (self.data/'result.json').write_bytes(b'altered')
        with self.assertRaisesRegex(ValueError,'checksum mismatch'):v.verify(self.manifest,repo_root=self.repo,artifact_root=self.data)
    def test_source_corruption(self):
        (self.repo/'source.py').write_bytes(b'altered')
        with self.assertRaisesRegex(ValueError,'checksum mismatch'):v.verify(self.manifest,repo_root=self.repo,archive=self.archive())
    def test_duplicate_tar_member(self):
        with self.assertRaisesRegex(ValueError,'duplicate'):v.verify(self.manifest,repo_root=self.repo,archive=self.archive(True))
    def test_path_outside_evidence(self):
        self.doc['artifacts'][0]['path']='../result.json';self.save()
        with self.assertRaisesRegex(ValueError,'relative evidence path'):v.verify(self.manifest,repo_root=self.repo,artifact_root=self.data)
if __name__=='__main__':unittest.main(verbosity=2)
