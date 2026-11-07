"""Guards fixed-byte transition provenance against archive/member/case corruption.
External integrity controls only; no Lean or source semantic proof.
"""
from pathlib import Path
import hashlib,importlib.util,io,json,tarfile,tempfile,unittest
O=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('transition',O/'verify-fixed-byte-transition.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
def rawsha(b):return hashlib.sha256(b).hexdigest()
def pack(path,raw):
 with tarfile.open(path,'w:gz') as t:
  i=tarfile.TarInfo('p.json');i.size=len(raw);t.addfile(i,io.BytesIO(raw))
def manifest(path,member):return {'archive':{'bytes':path.stat().st_size,'sha256':m.sha(path)},'files':[{'profile':'p.json','profileSha256':rawsha(member)}]}
class Integrity(unittest.TestCase):
 def test_profile_archive_and_member(self):
  with tempfile.TemporaryDirectory(dir=O/'artifacts') as tmp:
   p=Path(tmp)/'profile.tar.gz';raw=b'[]';pack(p,raw);d=manifest(p,raw)
   self.assertEqual(m.read_profiles(p,d),{'p.json':[]})
   p.write_bytes(p.read_bytes()+b'x')
   with self.assertRaisesRegex(AssertionError,'archive hash'):m.read_profiles(p,d)
   pack(p,b'[ ]');d=manifest(p,raw)
   with self.assertRaisesRegex(AssertionError,'member hash'):m.read_profiles(p,d)
 def fixture(self,tmp):
  p=Path(tmp)/'source.json';p.write_text('{"nodeType":"Block","statements":[]}')
  c={'fixture':str(p.relative_to(m.ROOT)),'fixtureSha256':m.sha(p),'pointer':'','nodeType':'Block','route':'statements','caseId':'test'}
  row={'nodeType':'Block','route':'statements','caseId':'test','producerExpression':None,'natural':{'status':'decoded','body':'[]'},'unknownRoot':{'status':'refused'}}
  return c,row
 def test_case_identity_and_fixture_hash(self):
  with tempfile.TemporaryDirectory(dir=O/'artifacts') as tmp:
   c,row=self.fixture(tmp);bad={**row,'caseId':'wrong'}
   with self.assertRaisesRegex(AssertionError,'identity'):m.compare([row],[bad],[c])
   m.cache.clear();c['fixtureSha256']='0'*64
   with self.assertRaisesRegex(AssertionError,'fixture hash'):m.compare([row],[row],[c])
 def test_address_witness_metadata(self):
  def declaration(metadata):
   return {'nodeType':'VariableDeclarationStatement','declarations':[{'typeName':metadata}]}
  self.assertTrue(m.address_witness(declaration({'name':'address','stateMutability':'nonpayable'})))
  for metadata in [{'name':'address'},{'name':'address','stateMutability':'payable'}]:
   self.assertFalse(m.address_witness(declaration(metadata)))
  self.assertFalse(m.address_witness({'nodeType':'TupleExpression','components':[{'typeDescriptions':{'typeString':'address payable'}}]}))
 def test_prior_decoded_behavior(self):
  with tempfile.TemporaryDirectory(dir=O/'artifacts') as tmp:
   c,row=self.fixture(tmp);bad={**row,'natural':{'status':'refused','reason':'changed'}}
   with self.assertRaisesRegex(AssertionError,'old decoded'):m.compare([row],[bad],[c])
if __name__=='__main__':unittest.main()
