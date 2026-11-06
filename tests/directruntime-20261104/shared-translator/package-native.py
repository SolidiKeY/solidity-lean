"""Package and verify native validation artifacts; never sends them anywhere."""
from pathlib import Path
import hashlib,json,subprocess,tarfile,io
root=Path(__file__).resolve().parents[3];o=Path(__file__).resolve().parent
native=o/'artifacts/native-3ad';e=o/'evidence/adoption-3ad';out=o/'artifacts/native-packet';out.mkdir(exist_ok=True)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
files={}
for name in ['direct-check','build.json','controls.json','initialize.c','ldd.txt','symbols.txt','runtime.stdout','runtime.stderr','runtime.strace','runtime.requests.jsonl','expected-api-results.json']:
 files['native/'+name]=native/name
for p in (native/'licenses').iterdir():files['native/licenses/'+p.name]=p
for p in (e/'frontend-origin').iterdir():files['frontend-origin/'+p.name]=p
files['native-build-config.json']=e/'native-build-config.json';files['rebase-e684.json']=e/'rebase-e684.json'
manifest={name:{'sha256':sha(p),'bytes':p.stat().st_size} for name,p in files.items()}
pack=out/'native-parity.tar.zst'
with pack.open('wb') as target:
 proc=subprocess.Popen(['zstd','-q','-T1','-3','-c'],stdin=subprocess.PIPE,stdout=target)
 with tarfile.open(fileobj=proc.stdin,mode='w|') as archive:
  for name,p in sorted(files.items()):archive.add(p,arcname=name,recursive=False)
  data=(json.dumps(manifest,indent=2)+'\n').encode();info=tarfile.TarInfo('CONTENTS.json');info.size=len(data);archive.addfile(info,io.BytesIO(data))
 proc.stdin.close();assert proc.wait()==0
proc=subprocess.Popen(['zstd','-dc',str(pack)],stdout=subprocess.PIPE);seen={}
with tarfile.open(fileobj=proc.stdout,mode='r|') as archive:
 for member in archive:
  assert member.isfile();data=archive.extractfile(member).read();assert member.name not in seen
  seen[member.name]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
  if member.name=='CONTENTS.json':assert json.loads(data)==manifest
for chunk in iter(lambda:proc.stdout.read(1048576),b''):assert not chunk.strip(b'\0')
assert proc.wait()==0;seen.pop('CONTENTS.json');assert seen==manifest
r={'pack':str(pack),'sha256':sha(pack),'bytes':pack.stat().st_size,'verifiedPayloadMembers':len(manifest),'binarySha256':sha(native/'direct-check'),'status':'verified-local; coordinator-pending','boundary':'Existing native producer build,18exact fixture comparisons+2failclosed,and reviewed candidate bodies. Not exhaustive closure,WASM,source preservation or full migration proof. No serialized Lean environments included.'}
(out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');(e/'native-packet-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
