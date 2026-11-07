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
    def detail_descriptor(self):
        data=json.dumps(self.manifest).encode();path=self.root/'detail.json';path.write_bytes(data)
        return {'schema_version':2,'detail_manifest':row('detail.json',data),'bulk_archive':self.manifest['archive']},path
    def test_missing_detail_cannot_bypass_checks(self):
        descriptor,path=self.detail_descriptor();self.assertIsNone(v.expand_manifest(descriptor));path.unlink();self.assertIsNone(v.expand_manifest(descriptor,path))
    def test_pinned_detail_preserves_all_original_checks(self):
        descriptor,path=self.detail_descriptor();expanded=v.expand_manifest(descriptor,path)
        self.assertEqual(expanded,self.manifest);self.assertEqual(v.verify(expanded,self.repo,self.evidence)['status'],'pass')
    def test_detail_tampering_refused(self):
        descriptor,path=self.detail_descriptor();path.write_text('{}')
        with self.assertRaisesRegex(ValueError,'DETAIL_MANIFEST_HASH_MISMATCH'):v.expand_manifest(descriptor,path)
    def test_detail_archive_link_mismatch_refused(self):
        descriptor,path=self.detail_descriptor();descriptor['bulk_archive']=row('other.tar.gz',b'other')
        with self.assertRaisesRegex(ValueError,'DETAIL_MANIFEST_DESCRIPTOR_MISMATCH'):v.expand_manifest(descriptor,path)
    def test_detail_base_mismatch_refused(self):
        descriptor,path=self.detail_descriptor();descriptor['base']='other'
        with self.assertRaisesRegex(ValueError,'DETAIL_MANIFEST_DESCRIPTOR_MISMATCH'):v.expand_manifest(descriptor,path)
    def test_detail_boolean_schema_refused(self):
        detail=dict(self.manifest,schema_version=True);data=json.dumps(detail).encode();path=self.root/'boolean.json';path.write_bytes(data)
        descriptor={'schema_version':2,'detail_manifest':row('boolean.json',data),'bulk_archive':self.manifest['archive']}
        with self.assertRaisesRegex(ValueError,'DETAIL_MANIFEST_DESCRIPTOR_MISMATCH'):v.expand_manifest(descriptor,path)
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
