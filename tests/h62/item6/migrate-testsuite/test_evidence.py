import hashlib,importlib.util,io,json,sys,tarfile,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'scripts/h62/item6/migrate-testsuite'))
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,ROOT/'scripts/h62/item6/migrate-testsuite'/file);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
v=load('verify_evidence','verify-evidence.py');api=load('public_api_portable','public-api-report.py')
def row(path,data):return {'path':path,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
class PortableEvidenceControls(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name);self.repo=self.root/'repo';self.repo.mkdir();self.evidence=self.root/'relocated';self.evidence.mkdir();(self.repo/'source').write_bytes(b'source');(self.evidence/'log').write_bytes(b'pass')
        self.manifest={'schema_version':1,'repository_files':[row('source',b'source')],'evidence_files':[row('log',b'pass')],'archive':row('evidence.tar.gz',b'unused')}
    def archive(self,members):
        path=self.root/'evidence.tar.gz'
        with tarfile.open(path,'w:gz') as tar:
            for name,data in members:
                info=tarfile.TarInfo(name);info.size=len(data);tar.addfile(info,io.BytesIO(data))
        self.manifest['archive']=row('evidence.tar.gz',path.read_bytes());return path
    def test_checkout_without_artifacts_is_pending(self):
        self.assertEqual(v.verify(self.manifest,self.repo)['status'],'pending_artifacts')
    def test_supplied_missing_directory_is_pending(self):
        self.assertEqual(v.verify(self.manifest,self.repo,self.root/'absent')['status'],'pending_artifacts')
    def test_supplied_missing_archive_is_pending(self):
        self.assertEqual(v.verify(self.manifest,self.repo,archive_path=self.root/'absent.tar.gz')['status'],'pending_artifacts')
    def test_missing_checkout_file_fails(self):
        (self.repo/'source').unlink()
        with self.assertRaisesRegex(ValueError,'MISSING_FILE'):v.verify(self.manifest,self.repo,self.evidence)
    def test_relocated_directory_verifies(self):
        self.assertEqual(v.verify(self.manifest,self.repo,self.evidence)['status'],'pass')
    def test_changed_checkout_refused(self):
        (self.repo/'source').write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError,'HASH_MISMATCH'):v.verify(self.manifest,self.repo,self.evidence)
    def test_changed_evidence_refused(self):
        (self.evidence/'log').write_bytes(b'fail')
        with self.assertRaisesRegex(ValueError,'HASH_MISMATCH'):v.verify(self.manifest,self.repo,self.evidence)
    def test_parent_path_refused(self):
        with self.assertRaisesRegex(ValueError,'INVALID_RELATIVE_PATH'):v.entries([row('../outside',b'')])
    def test_duplicate_manifest_refused(self):
        r=row('log',b'pass')
        with self.assertRaisesRegex(ValueError,'DUPLICATE_MANIFEST_PATH'):v.entries([r,r])
    def test_symlink_outside_root_refused(self):
        (self.evidence/'log').unlink();(self.evidence/'log').symlink_to(self.repo/'source')
        with self.assertRaisesRegex(ValueError,'PATH_ESCAPES_ROOT'):v.verify(self.manifest,self.repo,self.evidence)
    def test_archive_verified_without_extraction(self):
        path=self.archive([('evidence/log',b'pass')]);self.assertEqual(v.verify(self.manifest,self.repo,archive_path=path)['status'],'pass');self.assertFalse((self.root/'log').exists())
    def test_archive_tampering_refused(self):
        path=self.archive([('evidence/log',b'pass')]);path.write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError,'ARCHIVE_HASH_MISMATCH'):v.verify(self.manifest,self.repo,archive_path=path)
    def test_missing_archive_member_refused(self):
        path=self.archive([('evidence/other',b'pass')])
        with self.assertRaisesRegex(ValueError,'MISSING_ARCHIVE_MEMBERS'):v.verify(self.manifest,self.repo,archive_path=path)
    def test_duplicate_archive_member_refused(self):
        path=self.archive([('evidence/log',b'pass'),('evidence/log',b'pass')])
        with self.assertRaisesRegex(ValueError,'INVALID_ARCHIVE_MEMBER'):v.verify(self.manifest,self.repo,archive_path=path)
    def test_receipt_paths_relocate_explicitly(self):
        self.assertEqual(api.artifact_location('/old/capture/log',self.evidence,Path('/old/capture')),self.evidence/'log')
    def test_receipt_cannot_escape_relocated_root(self):
        with self.assertRaisesRegex(ValueError,'ARTIFACT_PATH_ESCAPES_ROOT'):api.artifact_location('../log',self.evidence)
if __name__=='__main__':unittest.main()
