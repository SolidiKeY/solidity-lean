"""Regression controls using in-memory manifest overlays; frozen bytes untouched."""
from pathlib import Path
from contextlib import redirect_stdout
from unittest.mock import patch
import copy,io,json,runpy,sys,traceback
sys.dont_write_bytecode=True
OWNED=Path(__file__).resolve().parent
sys.path.insert(0,str(OWNED))
from corpus_packet import verified_corpus,verified_readers

def execute(script):
 with redirect_stdout(io.StringIO()):runpy.run_path(str(OWNED/script),run_name='__main__')
# Successful complete verifications establish that failures below are the overlays.
execute('verify-corpus-inventory.py');execute('verify-corpus-readers.py')
scenarios=[
 ('corpus-inventory-manifest.json','counts','nodes','verify-corpus-inventory.py','census manifest count mismatch'),
 ('corpus-inventory-manifest.json','sourceBindingCounts','all-hashes-match','verify-corpus-inventory.py','source-binding count mismatch'),
 ('corpus-readers-manifest.json',None,'archiveSha256','verify-corpus-readers.py','archiveSha256'),
 ('corpus-readers-manifest.json',None,'filesManifestSha256','verify-corpus-readers.py','filesManifestSha256')]
for key in ['cases','default','composed','unknownRootRefusalsEachReader','changes','pairedNormalizedOccurrences','idFieldPresence','referenceFieldPresence']:
 scenarios.append(('corpus-readers-manifest.json',key if key in {'default','composed','changes','idFieldPresence','referenceFieldPresence'} else None,{'default':'decoded','composed':'decoded','changes':'refused->decoded','idFieldPresence':'both','referenceFieldPresence':'both'}.get(key,key),'verify-corpus-readers.py','manifest'))
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
   frames=traceback.extract_tb(error.__traceback__)
   assert marker in str(error) or any(marker in (frame.line or '') for frame in frames),(manifest,group,key,frames)
  else:raise AssertionError('changed manifest accepted: '+str((manifest,group,key)))
 results.append({'manifest':manifest,'field':(group+'.' if group else '')+key,'result':'refused'})
# Reauthenticate every frozen file after all overlays/verification rewrites.
verified_corpus();verified_readers()
print(json.dumps({'status':'pass','healthyVerifiers':2,'mutationsRejected':len(results),'cases':results,'boundary':'Only in-memory manifest reads changed;actual archives/manifests unchanged. No source/semantic proof claim.'}))
