"""Guards reproducible H90 all-occurrence archive integrity and member hashes.
Build artifacts are never ordinary verifier inputs or semantic certificates.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,tarfile
ROOT=Path(__file__).resolve().parents[3];OWNED=Path(__file__).resolve().parent
OUT=OWNED/'artifacts/h90';OCC=OWNED/'artifacts/occurrence-readers'
parser=argparse.ArgumentParser();parser.add_argument('--capture-manifest',action='store_true');args=parser.parse_args()
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
files=[OCC/n for n in ['cases.json','default.json','composed.json','summary.json']]
manifest=OWNED/'h90-occurrence-manifest.json'
if args.capture_manifest:
 data=json.loads(manifest.read_text());pack=OUT/'occurrence-pending.tar.zst'
 with pack.open('wb') as target:
  proc=subprocess.Popen(['zstd','-q','-T1','-3','-c'],stdin=subprocess.PIPE,stdout=target)
  with tarfile.open(fileobj=proc.stdin,mode='w|') as tar:
   for p in files:
    info=tar.gettarinfo(p,arcname=p.name);info.mtime=0;info.uid=0;info.gid=0;info.uname='';info.gname=''
    with p.open('rb') as src:tar.addfile(info,src)
  proc.stdin.close();assert proc.wait()==0
 digest=sha(pack);final=OUT/('occurrences-'+digest[:16]+'.tar.zst');pack.replace(final)
 data['archive']={'path':str(final),'archiveRelative':str(final.relative_to(ROOT)),'bytes':final.stat().st_size,'sha256':digest}
 data['files']=[{'path':str(p),'relative':str(p.relative_to(ROOT)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in files]
 data['summary']={k:v for k,v in json.loads((OCC/'summary.json').read_text()).items() if k!='perDocument'}
 manifest.write_text(json.dumps(data,indent=2)+'\n')
data=json.loads(manifest.read_text());expected={p.name:row for p,row in zip(files,data['files'],strict=True)}
for p,row in zip(files,data['files'],strict=True):
 assert row['relative']==str(p.relative_to(ROOT)) and p.stat().st_size==row['bytes'] and sha(p)==row['sha256']
assert data['summary']=={k:v for k,v in json.loads((OCC/'summary.json').read_text()).items() if k!='perDocument'}
a=data['archive'];pack=ROOT/a['archiveRelative'];assert pack.stat().st_size==a['bytes'] and sha(pack)==a['sha256']
proc=subprocess.Popen(['zstd','-dc',str(pack)],stdout=subprocess.PIPE);seen=set()
with tarfile.open(fileobj=proc.stdout,mode='r|') as tar:
 for member in tar:
  assert member.isfile() and member.name in expected and member.name not in seen;seen.add(member.name)
  row=expected[member.name];assert member.size==row['bytes'];h=hashlib.sha256();source=tar.extractfile(member)
  for chunk in iter(lambda:source.read(1048576),b''):h.update(chunk)
  assert h.hexdigest()==row['sha256']
for chunk in iter(lambda:proc.stdout.read(1048576),b''):assert not chunk.strip(b'\0')
assert proc.wait()==0 and seen==set(expected)
print(json.dumps({'archive':str(pack),'sha256':a['sha256'],'bytes':a['bytes'],'verifiedMembers':len(seen),'boundary':data['boundary']}))
