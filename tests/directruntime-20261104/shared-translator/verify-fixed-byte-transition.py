"""Guards H90 fixed-byte/address observation transitions and earlier admissions.
Finite decoder observations and source pointers are not semantic/source proofs.
"""
from pathlib import Path
import argparse,collections,hashlib,json,re,subprocess,tarfile
ROOT=Path(__file__).resolve().parents[3];O=Path(__file__).resolve().parent;OUT=O/'artifacts/fixed-bytes';BEFORE=OUT/'before'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def byte_witness(node):
 todo=[node]
 while todo:
  n=todo.pop()
  if isinstance(n,list):todo.extend(n)
  if not isinstance(n,dict):continue
  todo.extend(n.values())
  if n.get('nodeType')=='VariableDeclarationStatement':
   if any(isinstance(d,dict) and re.fullmatch(r'bytes(?:[1-9]|[12][0-9]|3[0-2])',d.get('typeName',{}).get('name','')) for d in n.get('declarations',[])):return True
  if n.get('nodeType')=='TupleExpression':
   if any(isinstance(c,dict) and re.fullmatch(r'bytes(?:[1-9]|[12][0-9]|3[0-2])',c.get('typeDescriptions',{}).get('typeString','')) for c in n.get('components',[])):return True
 return False
def address_witness(node):
 todo=[node]
 while todo:
  n=todo.pop()
  if isinstance(n,list):todo.extend(n)
  if not isinstance(n,dict):continue
  todo.extend(n.values())
  if n.get('nodeType')=='VariableDeclarationStatement':
   if any(isinstance(d,dict) and d.get('typeName',{}).get('name')=='address' and
          d.get('typeName',{}).get('stateMutability')=='nonpayable' for d in n.get('declarations',[])):return True
  if n.get('nodeType')=='TupleExpression':
   if any(isinstance(c,dict) and c.get('typeDescriptions',{}).get('typeString')=='address' for c in n.get('components',[])):return True
 return False
WITNESS=byte_witness
FAMILY='fixed-byte'
def read_profiles(pack,manifest):
 assert pack.stat().st_size==manifest['archive']['bytes'] and sha(pack)==manifest['archive']['sha256'],'prior profile archive hash'
 result={}
 with tarfile.open(pack,'r:gz') as t:
  for record in manifest['files']:
   name=Path(record['profile']).name;assert name not in result,'duplicate prior profile'
   member=t.getmember(name);assert member.isfile(),'nonregular prior profile'
   raw=t.extractfile(member).read();assert hashlib.sha256(raw).hexdigest()==record['profileSha256'],'prior profile member hash'
   result[name]=json.loads(raw)
 return result
cache={}
def fixture_node(c):
 path=ROOT/c['fixture']
 if path not in cache:
  assert sha(path)==c['fixtureSha256'],'fixture hash mismatch';cache[path]=json.loads(path.read_text())
 n=cache[path]
 for part in c['pointer'].split('/')[1:]:
  k=part.replace('~1','/').replace('~0','~');n=n[int(k)] if isinstance(n,list) else n[k]
 assert isinstance(n,dict) and n.get('nodeType')==c['nodeType'],'fixture pointer kind mismatch'
 return n
def witness(c):
 assert WITNESS(fixture_node(c)),'changed observation lacks '+FAMILY+' local/tuple witness'
def compare(old,new,cases):
 assert len(old)==len(new)==len(cases);changes=[]
 for a,b,c in zip(old,new,cases,strict=True):
  assert a['nodeType']==b['nodeType']==c['nodeType'] and a['route']==b['route']==c['route'],'case row mismatch'
  if 'caseId' in c:assert a['caseId']==b['caseId']==c['caseId'],'case identity mismatch'
  fixture_node(c)
  for key in ['caseId','nodeType','route','producerExpression']:
   if key in a:assert a[key]==b[key],('identity/producer drift',key)
  if c['route']!='none':assert a['unknownRoot']['status']==b['unknownRoot']['status']=='refused'
  if FAMILY=='environment':assert a==b,'environment increment changed decoder observation'
  if a['natural']['status']=='decoded':assert a['natural']==b['natural'],'old decoded behavior changed'
  if a==b:continue
  witness(c);changes.append({'caseId':c.get('caseId'),'fixture':c['fixture'],'pointer':c['pointer'],'before':a['natural'],'after':b['natural']})
 return changes
def main():
 global OUT, BEFORE, WITNESS, FAMILY
 parser=argparse.ArgumentParser();parser.add_argument('--capture-report',action='store_true');parser.add_argument('--family',choices=['fixed-byte','address','environment'],default='fixed-byte');args=parser.parse_args()
 FAMILY=args.family
 if FAMILY=='address':OUT=O/'artifacts/address';BEFORE=OUT/'before';WITNESS=address_witness
 if FAMILY=='environment':OUT=O/'artifacts/environment';BEFORE=OUT/'before'
 base=(OUT/'base-head.txt').read_text().strip();assert re.fullmatch('[0-9a-f]{40}',base)
 for name in ['h90-census-manifest.json','h90-reader-profile-manifest.json','h90-occurrence-manifest.json']:
  raw=subprocess.check_output(['git','show',base+':'+str((O/name).relative_to(ROOT))],cwd=ROOT);assert hashlib.sha256(raw).hexdigest()==sha(BEFORE/name)
 oldManifest=json.loads((BEFORE/'h90-reader-profile-manifest.json').read_text());profile=[]
 profilePack=ROOT/oldManifest['archive']['archiveRelative'];prior=read_profiles(profilePack,oldManifest)
 for record in oldManifest['files']:
  name=Path(record['profile']).name;old=prior[name];new=json.loads((O/'artifacts/h90/reader-profile'/name).read_text());legacy=ROOT/record['legacy']
  casepath=legacy.parent/('cases.json' if legacy.name in ['default.json','composed.json'] else legacy.name.removeprefix('composed-').replace('matrix','cases'))
  assert sha(casepath)==oldManifest['inputs'][str(casepath.relative_to(ROOT))],'prior case file hash'
  profile.extend(compare(old,new,json.loads(casepath.read_text())['cases']))
 a=json.loads((BEFORE/'census-results.json').read_text());b=json.loads((O/'artifacts/h90/cr-census-results.json').read_text());census=[]
 assert sha(BEFORE/'census-results.json')==json.loads((BEFORE/'h90-census-manifest.json').read_text())['archive']['files']['cr-census-results.json']
 for old,new in zip(a['rows'],b['rows'],strict=True):
  assert {k:v for k,v in old.items() if k!='canonical'}=={k:v for k,v in new.items() if k!='canonical'}
  if old==new:continue
  assert FAMILY!='environment','environment increment changed function admission/refusal'
  assert re.fullmatch(r'compact verifier: unsupported type '+('address' if FAMILY=='address' else r'bytes(?:[1-9]|[12][0-9]|3[0-2])'),old['canonical'])
  census.append({'identity':{k:old[k] for k in ['fixture','contract','function','sourceId']},'before':old['canonical'],'after':new['canonical']})
 occ=json.loads((BEFORE/'h90-occurrence-manifest.json').read_text());pack=ROOT/occ['archive']['archiveRelative'];assert sha(pack)==occ['archive']['sha256']
 casepath=O/'artifacts/occurrence-readers/cases.json'
 assert sha(casepath)==next(r['sha256'] for r in occ['files'] if Path(r['relative']).name=='cases.json'),'occurrence case hash'
 cases=json.loads(casepath.read_text())['cases'];occChanges={}
 p=subprocess.Popen(['zstd','-dc',str(pack)],stdout=subprocess.PIPE)
 with tarfile.open(fileobj=p.stdout,mode='r|') as t:
  for entry in t:
   if entry.name not in ['default.json','composed.json']:continue
   old=json.load(t.extractfile(entry));new=json.loads((O/'artifacts/occurrence-readers'/entry.name).read_text());occChanges[entry.name]=compare(old,new,cases)
 for chunk in iter(lambda:p.stdout.read(1048576),b''):pass
 assert p.wait()==0 and len(occChanges)==2
 result={'regression':'H90 '+FAMILY+' local observation transition','base':base,'profileChanges':len(profile),'profileTransitions':dict(collections.Counter(x['before']['status']+'->'+x['after']['status'] for x in profile)),'censusBefore':a['summary'],'censusAfter':b['summary'],'censusChanges':census,'occurrenceChanges':{k:len(v) for k,v in occChanges.items()},('priorDecodedOutcomesPreserved' if FAMILY=='environment' else 'priorDecodedBehaviorPreserved'):True,'unknownRootRefusalsPreserved':True,'boundary':FAMILY+' source witness/finite outcome checks, not decoded term equivalence, causal semantic or source adequacy proof.'}
 if args.capture_report:(OUT/'transition.json').write_text(json.dumps(result,indent=2)+'\n')
 else:assert json.loads((OUT/'transition.json').read_text())==result,'transition report mismatch'
 print(json.dumps(result))
if __name__=='__main__':main()
