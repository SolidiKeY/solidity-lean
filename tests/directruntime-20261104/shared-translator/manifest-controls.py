"""Regression controls using in-memory manifest overlays; frozen bytes untouched."""
from pathlib import Path
from contextlib import redirect_stdout
from unittest.mock import patch
import copy,io,json,runpy,sys
sys.dont_write_bytecode=True
OWNED=Path(__file__).resolve().parent
sys.path.insert(0,str(OWNED))
from corpus_packet import verified_corpus,verified_readers

def execute(script):
 with redirect_stdout(io.StringIO()),patch.object(sys,'argv',[script,'--read-only']),patch.object(Path,'write_text',side_effect=AssertionError('verifier attempted a write')):
  runpy.run_path(str(OWNED/script),run_name='__main__')
def frozen_state():
 state={}
 for directory in ['corpus-inventory','corpus-readers','h68-bulk']:
  root=OWNED/'artifacts'/directory
  for path in [root,*root.rglob('*')]:
   stat=path.stat();state[str(path)]=(stat.st_ino,stat.st_size,stat.st_mtime_ns,stat.st_ctime_ns)
 return state
before=frozen_state()
# Successful complete verifications establish that failures below are the overlays.
execute('verify-corpus-inventory.py');execute('verify-corpus-readers.py')
scenarios=[
 ('corpus-inventory-manifest.json','counts','nodes','verify-corpus-inventory.py','census manifest count mismatch'),
 ('corpus-inventory-manifest.json','sourceBindingCounts','all-hashes-match','verify-corpus-inventory.py','census manifest source-binding count mismatch'),
 ('corpus-readers-manifest.json',None,'archiveSha256','verify-corpus-readers.py','packet archive integrity mismatch'),
 ('corpus-readers-manifest.json',None,'filesManifestSha256','verify-corpus-readers.py','packet files manifest integrity mismatch')]
for key in ['cases','default','composed','unknownRootRefusalsEachReader','changes','pairedNormalizedOccurrences','idFieldPresence','referenceFieldPresence']:
 scenarios.append(('corpus-readers-manifest.json',key if key in {'default','composed','changes','idFieldPresence','referenceFieldPresence'} else None,{'default':'decoded','composed':'decoded','changes':'refused->decoded','idFieldPresence':'both','referenceFieldPresence':'both'}.get(key,key),'verify-corpus-readers.py','reader manifest transition mismatch' if key=='changes' else 'reader manifest count mismatch: '+key))
results=[];original=Path.read_text
for manifest,group,key,script,marker in scenarios:
 target=OWNED/manifest;altered=copy.deepcopy(json.loads(original(target)))
 container=altered[group] if group else altered
 container[key]='0'*64 if key.endswith('Sha256') else container[key]+1
 def overlay(self,*args,**kwargs):
  return json.dumps(altered) if self==target else original(self,*args,**kwargs)
 with patch.object(Path,'read_text',overlay):
  try:execute(script)
  except AssertionError as error:
   assert str(error)==marker,(manifest,group,key,str(error),marker)
  else:raise AssertionError('changed manifest accepted: '+str((manifest,group,key)))
 results.append({'manifest':manifest,'field':(group+'.' if group else '')+key,'result':'refused'})
# Reauthenticate every frozen file after all read-only overlays/verifications.
verified_corpus();verified_readers()
assert frozen_state()==before, 'frozen artifact metadata changed'
print(json.dumps({'status':'pass','healthyVerifiers':2,'mutationsRejected':len(results),'frozenMetadataUnchanged':True,'cases':results,'boundary':'Only in-memory manifest reads changed;actual archives/manifests unchanged. No source/semantic proof claim.'}))
