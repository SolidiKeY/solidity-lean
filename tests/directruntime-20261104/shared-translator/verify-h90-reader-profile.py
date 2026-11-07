"""Guards H90 reader regression profiles against immutable prior snapshots.
Only narrow-local/tuple-leaf admissions or refusal refinements may differ.
This checks finite decoder observations, not source or intrinsic adequacy.
"""
from pathlib import Path
import argparse,collections,hashlib,json,re,tarfile,gzip,io
ROOT=Path(__file__).resolve().parents[3];OWNED=Path(__file__).resolve().parent
OUT=OWNED/'artifacts/h90';PROFILE=OUT/'reader-profile'
parser=argparse.ArgumentParser();parser.add_argument('--capture-manifest',action='store_true');args=parser.parse_args()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def narrow(s):
 if s=="address":return True
 b=re.fullmatch(r'bytes([0-9]+)',s or '')
 if b:return str(int(b[1]))==b[1] and 1<=int(b[1])<=32
 m=re.fullmatch(r'(?:uint|int)([0-9]+)',s or '')
 return bool(m and str(int(m[1]))==m[1] and 8<=int(m[1])<256 and int(m[1])%8==0)
def nodes(value):
 todo=[value]
 while todo:
  v=todo.pop()
  if isinstance(v,dict):
   yield v;todo.extend(v.values())
  elif isinstance(v,list):todo.extend(v)
def narrow_witness(root):
 for n in nodes(root):
  if n.get('nodeType')=='VariableDeclarationStatement':
   for d in n.get('declarations',[]):
    if isinstance(d,dict):
     t=d.get('typeName',{})
     if t.get('nodeType')=='ElementaryTypeName' and narrow(t.get('name')):return True
  if n.get('nodeType')=='TupleExpression':
   if any(isinstance(c,dict) and narrow(c.get('typeDescriptions',{}).get('typeString')) for c in n.get('components',[])):return True
 return False
cache={};inputs={};records=[];changes=[]
paths=sorted(PROFILE.glob('*.json'));assert len(paths)==8,'H90 profile file count'
for new in paths:
 legacy=ROOT/new.name.replace('__','/');old=json.loads(legacy.read_text());current=json.loads(new.read_text())
 if legacy.name in ['default.json','composed.json']:casepath=legacy.parent/'cases.json'
 else:casepath=legacy.parent/legacy.name.removeprefix('composed-').replace('matrix','cases')
 cases=json.loads(casepath.read_text())['cases'];assert len(old)==len(current)==len(cases)
 inputs[str(casepath.relative_to(ROOT))]=sha(casepath)
 delta=[]
 for index,(a,b,c) in enumerate(zip(old,current,cases,strict=True)):
  for field in ['nodeType','route']:assert a[field]==b[field]==c[field]
  if 'caseId' in c:assert a['caseId']==b['caseId']==c['caseId']
  assert a['producerExpression']==b['producerExpression'],'producer observation changed'
  if c['route']=='none':assert a==b and b['unknownRoot'] is None
  else:assert a['unknownRoot']['status']==b['unknownRoot']['status']=='refused','unknown-root admission'
  fixture=ROOT/c['fixture']
  if fixture not in cache:
   assert sha(fixture)==c['fixtureSha256'],'fixture integrity'
   cache[fixture]=json.loads(fixture.read_text())
   inputs[c['fixture']]=c['fixtureSha256']
  if a==b:continue
  assert c['route'] in ['expression','statements','function'],'unrelated route changed'
  assert {k:v for k,v in a.items() if k not in ['natural','unknownRoot']}=={k:v for k,v in b.items() if k not in ['natural','unknownRoot']}
  assert a['natural']['status']=='refused' and b['natural']['status'] in ['refused','decoded'],'admission downgrade'
  node=cache[fixture]
  for part in c['pointer'].split('/')[1:]:
   key=part.replace('~1','/').replace('~0','~');node=node[int(key)] if isinstance(node,list) else node[key]
  assert narrow_witness(node),'changed witness outside H90 narrow/fixed-byte/address local scope'
  row={'snapshot':str(legacy.relative_to(ROOT)),'index':index,'fixture':c['fixture'],'pointer':c['pointer'],'before':a,'after':b}
  changes.append(row);delta.append(row)
 records.append({'legacy':str(legacy.relative_to(ROOT)),'legacySha256':sha(legacy),'profile':str(new.relative_to(ROOT)),'profileSha256':sha(new),'rows':len(current),'changes':len(delta),'transitions':dict(collections.Counter(r['before']['natural']['status']+'->'+r['after']['natural']['status'] for r in delta))})
summary={'regression':'H90 narrow/fixed-byte/address local reader observations','files':records,'inputs':inputs,'changes':len(changes),'rows':sum(r['rows'] for r in records),'boundary':'Historical snapshots untouched. Finite decoder/diagnostic controls only; no source, overload, intrinsic or backend proof.'}
manifest=OWNED/'h90-reader-profile-manifest.json'
if args.capture_manifest:
 (OUT/'reader-profile-changes.json').write_text(json.dumps(changes,indent=2)+'\n')
 data=io.BytesIO()
 with gzip.GzipFile(fileobj=data,mode='wb',mtime=0) as compressed:
  with tarfile.open(fileobj=compressed,mode='w') as archive:
   for f in paths+[OUT/'reader-profile-changes.json']:
    raw=f.read_bytes();entry=tarfile.TarInfo(f.name);entry.size=len(raw);entry.mtime=0;archive.addfile(entry,io.BytesIO(raw))
 raw=data.getvalue();digest=hashlib.sha256(raw).hexdigest();pack=OUT/('reader-profile-'+digest[:16]+'.tar.gz');pack.write_bytes(raw)
 summary['archive']={'path':str(pack),'archiveRelative':str(pack.relative_to(ROOT)),'sha256':digest,'bytes':len(raw)}
 manifest.write_text(json.dumps(summary,indent=2)+'\n')
else:
 expected=json.loads(manifest.read_text());archive=expected.pop('archive');assert summary==expected,'profile manifest mismatch'
 pack=ROOT/archive['archiveRelative'];assert pack.stat().st_size==archive['bytes'] and sha(pack)==archive['sha256'],'profile archive integrity'
 expectedFiles={p.name:p.read_bytes() for p in paths};expectedFiles['reader-profile-changes.json']=(OUT/'reader-profile-changes.json').read_bytes();seen=set()
 with tarfile.open(pack,'r:gz') as tar:
  for entry in tar:
   assert entry.isfile() and entry.name in expectedFiles and entry.name not in seen;seen.add(entry.name)
   assert tar.extractfile(entry).read()==expectedFiles[entry.name]
 assert seen==set(expectedFiles)
print(json.dumps({'files':len(records),'rows':summary['rows'],'changes':len(changes),'transitions':dict(collections.Counter(r['before']['natural']['status']+'->'+r['after']['natural']['status'] for r in changes)),'scope':'narrow/fixed-byte/address locals/tuple leaves only; unknown roots refused'}))
