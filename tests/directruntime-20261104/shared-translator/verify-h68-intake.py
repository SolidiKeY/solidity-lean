"""Guards H68 metadata-only fixture migration and exact shared hash re-pins.
Reads pinned Git blobs; does not migrate live fixtures or claim Lean/runtime parity.
"""
from pathlib import Path
import argparse,collections,hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[3]
APPLY='c0c53877f279964b86d55f56ea0bba4ec440a788'
CORRECTED='e13535d56684c196ba011ad1f07f373314ee1105'
HEAD='19a7a1a9f764b19e75b16a9f941618a33a1678cf'
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def blob(rev,path):return git('show',rev+':'+path)
def digest(raw):return hashlib.sha256(raw).hexdigest()
def strip_metadata(value):
 if isinstance(value,dict):return {k:strip_metadata(v) for k,v in value.items() if k not in ('typeIdentifier','tryCall')}
 if isinstance(value,list):return [strip_metadata(v) for v in value]
 return value
def field_counts(value):
 counts=collections.Counter();todo=[value]
 while todo:
  v=todo.pop()
  if isinstance(v,dict):
   counts.update(k for k in v if k in ('typeIdentifier','tryCall'));todo.extend(v.values())
  elif isinstance(v,list):todo.extend(v)
 return dict(counts)
def replace_hashes(value,pairs):
 if isinstance(value,str):
  for old,new in pairs:value=value.replace(old,new)
  return value
 if isinstance(value,list):return [replace_hashes(v,pairs) for v in value]
 if isinstance(value,dict):return {k:replace_hashes(v,pairs) for k,v in value.items()}
 return value
def verify():
 for a,b in [(APPLY,CORRECTED),(CORRECTED,HEAD)]:subprocess.run(['git','merge-base','--is-ancestor',a,b],cwd=ROOT,check=True)
 parent=git('rev-parse',APPLY+'^').decode().strip()
 receipt=json.loads(blob(APPLY,'tests/cr-canonical-reader/h68-migration-applied.json'))
 rows=[r for r in receipt['fixtures'] if r.get('applied')]
 assert len(rows)==34 and len({r['fixture'] for r in rows})==34 and all(r['status']=='exact' for r in rows)
 changedFixtures={p for p in git('diff','--name-only',parent,APPLY,'--','tests/solc').decode().splitlines() if p.endswith('.ast.json')}
 assert changedFixtures=={r['fixture'] for r in rows},'fixture changed-set mismatch'
 fixtures={};fields=collections.Counter()
 for r in rows:
  path=r['fixture'];old=blob(parent,path);new=blob(APPLY,path)
  assert digest(old)==r['oldSha256'] and digest(new)==r['newSha256'],('fixture hash',path)
  assert blob(HEAD,path)==new,('current CR fixture drift',path)
  a,b=json.loads(old),json.loads(new)
  assert a['header']==b['header'],('header changed',path)
  assert strip_metadata(a)==strip_metadata(b),('non-metadata drift',path)
  fields.update(field_counts(b));fixtures[path]={'oldSha256':digest(old),'newSha256':digest(new),'bytes':len(new)}
 pins=json.loads(blob(APPLY,'tests/cr-canonical-reader/shared-translator-repins.json'))['pins']
 assert len(pins)==44 and len({(r['file'],r['fixture']) for r in pins})==44 and sum(r['occurrences'] for r in pins)==861
 grouped=collections.defaultdict(list)
 for r in pins:
  assert r['fixture'] in fixtures and all(r[k]==fixtures[r['fixture']][k] for k in ['oldSha256','newSha256'])
  before=blob(parent,r['file']).decode();after=blob(CORRECTED,r['file']).decode()
  assert before.count(r['oldSha256'])==r['occurrences'],('old count',r['file'])
  assert after.count(r['newSha256'])==r['occurrences'] and r['oldSha256'] not in after,('new count',r['file'])
  grouped[r['file']].append((r['oldSha256'],r['newSha256']))
 assert len(grouped)==5
 changedShared=set(git('diff','--name-only',parent,APPLY,'--','tests/directruntime-20261104/shared-translator').decode().splitlines())
 assert changedShared==set(grouped),'shared changed-set mismatch'
 for path,pairs in grouped.items():
  assert replace_hashes(json.loads(blob(parent,path)),pairs)==json.loads(blob(CORRECTED,path)),('not hash-only',path)
  assert blob(HEAD,path)==blob(CORRECTED,path),('current CR shared drift',path)
 lean=[p for p in git('diff','--name-only',parent,APPLY).decode().splitlines() if p.endswith('.lean')]
 assert len(lean)==20
 changed=0
 for path in lean:
  a,b=blob(parent,path).decode(),blob(APPLY,path).decode()
  assert blob(HEAD,path)==blob(APPLY,path),('current CR Lean drift',path)
  pattern=r'(?<=hash )0x[0-9a-fA-F]+'
  assert re.sub(pattern,'<fixture-hash>',a)==re.sub(pattern,'<fixture-hash>',b),('Lean non-pin drift',path)
  x,y=re.findall(pattern,a),re.findall(pattern,b);assert len(x)==len(y)
  changed+=sum(u!=v for u,v in zip(x,y))
 assert changed==128
 return {'regression':'H68 metadata-only migration and shared fixture hash re-pins','apply':APPLY,'corrected':CORRECTED,'observedCrHead':HEAD,'parent':parent,'fixtures':fixtures,'fixtureCount':34,'sharedPinEntries':44,'sharedPinOccurrences':861,'sharedFiles':sorted(grouped),'leanPinModules':20,'changedLeanHashLiterals':128,'metadataFieldsPresentAfter':dict(fields),'boundary':'Git-blob identity/metadata/hash-only verification. Not compiler replay, Lean proof checking, reader-outcome re-observation, importer migration or H102 acceptance.'}
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path);args=parser.parse_args();result=verify()
 if args.output:args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='fixtures'}))
