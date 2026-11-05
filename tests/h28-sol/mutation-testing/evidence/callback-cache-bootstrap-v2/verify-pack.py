from pathlib import Path
import json,hashlib,tarfile,time
out=Path(__file__).resolve().parent;r=json.loads((out/'cache-pack.json').read_text());t=time.monotonic()
def sha(f):
 h=hashlib.sha256()
 for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
with open(r['archive'],'rb') as f:assert sha(f)==r['sha256']
with tarfile.open(r['archive'],'r:gz') as tar:
 expected={}
 for line in tar.extractfile('SHA256SUMS').read().decode().splitlines():
  h,p=line.split('  ',1);assert p not in expected;expected[p]=h
 seen=set()
 for member in tar:
  assert member.isfile() and member.name not in seen
  assert not member.name.startswith('/') and '..' not in Path(member.name).parts
  seen.add(member.name)
  if member.name!='SHA256SUMS':assert sha(tar.extractfile(member))==expected[member.name]
 assert seen==set(expected)|{'SHA256SUMS'}
 manifest=tar.extractfile('cache-manifest.json').read();assert hashlib.sha256(manifest).hexdigest()==r['cache_manifest_sha256'];m=json.loads(manifest)
 assert m['complete'] and len(m['artifact_sha256'])==71 and len(m['reused_artifact_sha256'])==68 and len(m['checks'])==3
 for c in m['checks']:
  mod=c['module'].replace('.','/');assert sha(tar.extractfile('cache/'+mod+'.olean'))==m['artifact_sha256'][mod+'.olean'];assert sha(tar.extractfile('sources/'+mod+'.lean'))==m['source_sha256'][mod+'.lean']
 assert tar.extractfile('catalog.json').read()==(out/'catalog.json').read_bytes()
with open(r['dependency_pack']['archive'],'rb') as f:assert sha(f)==r['dependency_pack']['sha256']
print(json.dumps({'status':'pass','command':'python3 -B '+str(Path(__file__).resolve()),'archive':r['archive'],'regular_members':len(seen),'new_artifacts':3,'total_cache_artifacts':71,'dependency_pack_hash_verified':True,'seconds':time.monotonic()-t,'coordinator_pull_observed':False},indent=2))
