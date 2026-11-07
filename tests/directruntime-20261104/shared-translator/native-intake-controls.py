"""Guards native evidence intake against traversal, symlink redirects and false stack mapping.
These are external integrity tests, not Lean or runtime correctness proofs.
"""
from pathlib import Path
import importlib.util,tempfile,unittest
OWNED=Path(__file__).resolve().parent
def module(name,file):
 spec=importlib.util.spec_from_file_location(name,OWNED/file);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
intake=module('native_intake','verify-native-intake.py');diagnosis=module('native_diagnosis','diagnose-native-evidence.py')
class IntegrityControls(unittest.TestCase):
 def test_healthy_archive(self):self.assertEqual(len(intake.verify(intake.DEFAULT)['members']),10)
 def test_unsafe_names(self):
  for name in ['/absolute','../outside','a/../outside','a//b','a/./b','.']:
   with self.subTest(name=name),self.assertRaises(AssertionError):intake.safe_name(name)
 def test_symlink_ancestors(self):
  with tempfile.TemporaryDirectory(dir=OWNED/'artifacts') as tmp:
   root=Path(tmp);outside=root/'outside';outside.mkdir();alias=root/'alias';alias.symlink_to(outside,target_is_directory=True)
   with self.assertRaisesRegex(AssertionError,'symlink'):intake.safe_target(alias,'file')
   base=root/'base';base.mkdir();(base/'.lake').symlink_to(outside,target_is_directory=True)
   with self.assertRaisesRegex(AssertionError,'symlink'):intake.safe_target(base,'.lake/escape/file')
   self.assertEqual(list(outside.iterdir()),[])
 def test_leaf_symlink(self):
  with tempfile.TemporaryDirectory(dir=OWNED/'artifacts') as tmp:
   root=Path(tmp);(root/'link').symlink_to(root/'missing')
   with self.assertRaisesRegex(AssertionError,'symlink'):intake.safe_target(root,'link')
 def test_archive_tamper(self):
  with tempfile.TemporaryDirectory(dir=OWNED/'artifacts') as tmp:
   path=Path(tmp)/'mutated.tar.gz';raw=intake.DEFAULT.read_bytes();path.write_bytes(b'!'+raw[1:])
   with self.assertRaisesRegex(AssertionError,'archive hash'):intake.verify(path)
 def test_frame_bounds_and_export(self):
  layout={'imports':1,'bodies':[(100,150)],'exports':{1:'root'}}
  self.assertEqual(diagnosis.frame_locations('wasm-function[1]:0x64',layout)[0]['export'],'root')
  with self.assertRaisesRegex(AssertionError,'outside'):diagnosis.frame_locations('wasm-function[1]:0x96',layout)
  with self.assertRaises(AssertionError):diagnosis.frame_locations('wasm-function[0]:0x64',layout)
 def test_truncated_wasm_section(self):
  with self.assertRaisesRegex(AssertionError,'section length'):diagnosis.wasm_layout(b'\0asm\x01\0\0\0\x01\x20')
 def test_incomplete_saved_rounds(self):
  with self.assertRaises(AssertionError):diagnosis.benchmark_summary([{'name':'only','wallMs':1}])
if __name__=='__main__':unittest.main()
