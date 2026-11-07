"""Negative controls for occurrence accounting; never mutates frozen packets."""
from pathlib import Path
from unittest.mock import patch
import contextlib,io,json,runpy,sys
sys.dont_write_bytecode=True
OWNED=Path(__file__).resolve().parent
sys.path.insert(0,str(OWNED))
from corpus_packet import verified_corpus
verifier=OWNED/'verify-occurrence-readers.py'
casePath=OWNED/'artifacts/occurrence-readers/cases.json'
originalRead=Path.read_text
original=originalRead(casePath)

def check(name,mutate,marker):
 packet=json.loads(original)
 if mutate is not None:mutate(packet)
 replacement=json.dumps(packet)
 def read(path,*args,**kwargs):
  return replacement if path==casePath else originalRead(path,*args,**kwargs)
 try:
  with patch.object(Path,'write_text',side_effect=AssertionError('unexpected write')),patch.object(Path,'write_bytes',side_effect=AssertionError('unexpected write')),patch.object(Path,'read_text',read),patch.object(sys,'argv',[str(verifier),'--cases-only']),contextlib.redirect_stdout(io.StringIO()):
   runpy.run_path(str(verifier),run_name='__main__')
 except AssertionError as error:
  if mutate is None:raise
  assert str(error)==marker, 'wrong rejection for '+name+': '+str(error)
  traceback=error.__traceback__
  while traceback.tb_next:traceback=traceback.tb_next
  assert Path(traceback.tb_frame.f_code.co_filename)==verifier, 'failure outside verifier'
  return {'case':name,'result':'rejected','line':traceback.tb_lineno}
 assert mutate is None, 'corrupted witness was accepted: '+name
 return {'case':name,'result':'accepted'}

controls=[('healthy',None,None),
 ('missing-occurrence',lambda p:p['cases'].pop(),'occurrence count mismatch'),
 ('case-identity',lambda p:p['cases'][0].__setitem__('caseId','0'*64),'occurrence identity mismatch'),
 ('pointer',lambda p:p['cases'][0].__setitem__('pointer','/invalid'),'occurrence witness field mismatch: pointer'),
 ('node-hash',lambda p:p['cases'][0].__setitem__('nodeSha256','0'*64),'occurrence witness field mismatch: nodeSha256'),
 ('route',lambda p:p['cases'][0].__setitem__('route','invalid'),'occurrence route mismatch')]
results=[check(name,mutate,marker) for name,mutate,marker in controls]
verified_corpus()
assert originalRead(casePath)==original
print(json.dumps({'controls':results,'boundary':'External integrity controls only; no Lean or semantic proof.'}))
