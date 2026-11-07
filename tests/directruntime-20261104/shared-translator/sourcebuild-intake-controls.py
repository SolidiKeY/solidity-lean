"""Guards sourceBuild1e8 intake rejection of duplicate, unsafe and altered inputs.
These external Python checks establish verifier behavior, not Lean/source adequacy.
"""
import importlib.util, io, tarfile, tempfile, unittest
from pathlib import Path
spec = importlib.util.spec_from_file_location('intake', Path(__file__).with_name('verify-sourcebuild-intake.py'))
intake = importlib.util.module_from_spec(spec)
spec.loader.exec_module(intake)
class Controls(unittest.TestCase):
 def archive(self, names, kind=tarfile.REGTYPE):
  stream = io.BytesIO()
  with tarfile.open(fileobj=stream,mode='w') as out:
   for name in names:
    entry = tarfile.TarInfo(name); entry.type = kind
    out.addfile(entry,io.BytesIO())
  stream.seek(0)
  return tarfile.open(fileobj=stream,mode='r:')
 def test_unsafe_members(self):
  for name in ['../escape','/absolute','a/../b','./x']:
   with self.subTest(name=name), self.archive([name]) as tar:
    with self.assertRaises(ValueError): intake.members(tar)
 def test_duplicate_and_link(self):
  with self.archive(['same','same']) as tar:
   with self.assertRaisesRegex(ValueError,'duplicate'): intake.members(tar)
  with self.archive(['link'],tarfile.SYMTYPE) as tar:
   with self.assertRaisesRegex(ValueError,'unsafe'): intake.members(tar)
 def test_altered_archive(self):
  with tempfile.TemporaryDirectory() as tmp:
   root = Path(tmp); (root/'evidence.tar.gz').write_bytes(b'wrong bytes')
   with self.assertRaisesRegex(ValueError,'outer archive/manifest hash'): intake.verify(root)
if __name__ == '__main__': unittest.main()
