"""Guard validation restoration against path escape, stale bytes and source overwrite.
Synthetic data-tree controls only; no Lean, source compiler or runtime execution.
"""
import copy,hashlib,importlib.util,io,json,pathlib,tarfile,tempfile,unittest
spec=importlib.util.spec_from_file_location('inputs',pathlib.Path(__file__).with_name('validation-inputs.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class Controls(unittest.TestCase):
 def fixture(self,root):
  tracked={'tests/solc/read-only.json'}
  paths={'tests/solc/read-only.json':b'tracked',m.ART+'sample.json':b'original'}
  rows=[{'path':p,'bytes':len(raw),'sha256':m.sha(raw),'tracked':p in tracked} for p,raw in paths.items()]
  manifest={'files':rows};(root/'tests/solc').mkdir(parents=True);(root/'tests/solc/read-only.json').write_bytes(b'tracked')
  archive=root/'inputs.tar.gz';self.archive(archive,{p:raw for p,raw in paths.items() if p not in tracked})
  manifest['archive']={'sha256':m.sha(archive.read_bytes()),'bytes':archive.stat().st_size}
  return manifest,archive,tracked
 def archive(self,path,files,extra=None):
  with tarfile.open(path,'w:gz') as tar:
   for name,raw in files.items():
    info=tarfile.TarInfo(name);info.size=len(raw);tar.addfile(info,io.BytesIO(raw))
   if extra:tar.addfile(extra)
 def test_missing_restore_and_idempotence(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=pathlib.Path(tmp);manifest,archive,tracked=self.fixture(root)
   self.assertEqual(m.check(root,manifest,tracked)['missing'],[m.ART+'sample.json'])
   self.assertEqual(m.restore(root,manifest,archive,tracked)['restored'],1)
   self.assertEqual(m.restore(root,manifest,archive,tracked)['restored'],0)
 def test_changed_tracked_or_existing_data_never_overwritten(self):
  for name in ['tests/solc/read-only.json',m.ART+'sample.json']:
   with tempfile.TemporaryDirectory() as tmp:
    root=pathlib.Path(tmp);manifest,archive,tracked=self.fixture(root);path=root/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(b'changed')
    with self.assertRaisesRegex(ValueError,'refusing overwrite'):m.restore(root,manifest,archive,tracked)
    self.assertEqual(path.read_bytes(),b'changed')
 def test_archive_corruption_and_extra_member_rejected(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=pathlib.Path(tmp);manifest,archive,tracked=self.fixture(root)
   archive.write_bytes(b'bad')
   with self.assertRaisesRegex(ValueError,'archive hash'):m.restore(root,manifest,archive,tracked)
   self.archive(archive,{m.ART+'sample.json':b'wrong payload'})
   manifest['archive']={'sha256':m.sha(archive.read_bytes()),'bytes':archive.stat().st_size}
   with self.assertRaisesRegex(ValueError,'member hash'):m.restore(root,manifest,archive,tracked)
   self.archive(archive,{m.ART+'sample.json':b'original','unexpected.json':b'extra'})
   manifest['archive']={'sha256':m.sha(archive.read_bytes()),'bytes':archive.stat().st_size}
   with self.assertRaisesRegex(ValueError,'member set'):m.restore(root,manifest,archive,tracked)
   self.assertFalse((root/(m.ART+'sample.json')).exists())
 def test_escape_symlink_and_tracked_reclassification(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=pathlib.Path(tmp);manifest,archive,tracked=self.fixture(root)
   for name in ['/absolute','../escape',m.ART+'../escape.json']:
    with self.assertRaises(ValueError):m.target(root,name)
   (root/'linked').symlink_to(root/'tests',target_is_directory=True)
   with self.assertRaisesRegex(ValueError,'symlink'):m.target(root,'linked/solc/read-only.json')
   manifest['files'][0]['tracked']=False
   with self.assertRaisesRegex(ValueError,'classification'):m.check(root,manifest,tracked)
 def test_all_missing_reported_and_missing_tracked_not_restored(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=pathlib.Path(tmp);manifest,archive,tracked=self.fixture(root);(root/'tests/solc/read-only.json').unlink()
   self.assertEqual(len(m.check(root,manifest,tracked)['missing']),2)
   with self.assertRaisesRegex(ValueError,'missing tracked'):m.restore(root,manifest,archive,tracked)
   self.assertFalse((root/(m.ART+'sample.json')).exists())
 def test_real_snapshot_in_synthetic_data_tree(self):
  manifest=json.loads(m.MANIFEST.read_text());tracked={r['path'] for r in manifest['files'] if r['tracked']}
  with tempfile.TemporaryDirectory() as tmp:
   root=pathlib.Path(tmp)
   for row in manifest['files']:
    if row['tracked']:
     path=root/row['path'];path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes((m.ROOT/row['path']).read_bytes())
   before=m.check(root,manifest,tracked);self.assertEqual(len(before['missing']),sum(not r['tracked'] for r in manifest['files']))
   result=m.restore(root,manifest,m.ROOT/manifest['archive']['repositoryRelative'],tracked)
   self.assertEqual(result['restored'],len(before['missing']))
   self.assertEqual(m.check(root,manifest,tracked),{'missing':[],'changed':[],'files':len(manifest['files'])})
if __name__=='__main__':unittest.main()
