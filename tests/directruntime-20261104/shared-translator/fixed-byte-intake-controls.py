"""Guards fixed-byte intake against altered indexes, payloads and saved parity drift.
External verifier controls only; no Lean or source/compiler adequacy proof.
"""
import copy,hashlib,importlib.util,io,json,tarfile,tempfile,unittest
from pathlib import Path
O=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('fixed_intake',O/'verify-fixed-byte-intake.py')
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
class Controls(unittest.TestCase):
 def test_timing_projection(self):
  row={'name':'x','wireSha256':'wire','reply':{'results':[{'status':'proved','sourceId':7}]}}
  browser=copy.deepcopy(row);browser['boot']={'build':'wasm'};browser['reply']['timings']={'checkMs':17}
  self.assertEqual(m.parity({'native':[row],'browser':[browser]},1,'wasm')['statuses'],{'proved':1})
 def test_wire_result_and_binary_drift(self):
  row={'name':'x','wireSha256':'wire','reply':{'results':[{'status':'proved','sourceId':7}]}}
  for field in ['wire','status','identity','binary']:
   with self.subTest(field=field):
    browser=copy.deepcopy(row);browser['boot']={'build':'wasm'}
    if field=='wire':browser['wireSha256']='different'
    if field=='status':browser['reply']['results'][0]['status']='unsupported'
    if field=='identity':browser['reply']['results'][0]['sourceId']=8
    if field=='binary':browser['boot']['build']='different'
    with self.assertRaises(ValueError):m.parity({'native':[row],'browser':[browser]},1,'wasm')
 def test_duplicate_case_identity(self):
  row={'name':'x','wireSha256':'wire','reply':{'results':[{'status':'proved'}]}}
  browser={**row,'boot':{'build':'wasm'}}
  with self.assertRaisesRegex(ValueError,'duplicate request identity'):
   m.parity({'native':[row,row],'browser':[browser,browser]},2,'wasm')
 def test_index_and_member_integrity(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);index=root/'index.json';archive=root/'payload.tar.gz'
   expected=b'abc';records=[{'path':'payload','bytes':3,'sha256':hashlib.sha256(expected).hexdigest()}]
   index.write_text(json.dumps(records))
   def write(payload,duplicate=False):
    with tarfile.open(archive,'w:gz') as tar:
     pairs=[('payload',payload),('index.json',index.read_bytes())]
     if duplicate:pairs.append(('payload',payload))
     for name,raw in pairs:
      member=tarfile.TarInfo(name);member.size=len(raw);tar.addfile(member,io.BytesIO(raw))
   write(expected);self.assertEqual(m.indexed_archive(archive,index,1),{'payload':expected})
   write(b'xyz')
   with self.assertRaisesRegex(ValueError,'member hash'):m.indexed_archive(archive,index,1)
   write(expected,True)
   with self.assertRaisesRegex(ValueError,'duplicate'):m.indexed_archive(archive,index,1)
   write(expected);index.write_text(json.dumps([{**records[0],'sha256':'0'*64}]))
   with self.assertRaisesRegex(ValueError,'embedded index'):m.indexed_archive(archive,index,1)
if __name__=='__main__':unittest.main()
