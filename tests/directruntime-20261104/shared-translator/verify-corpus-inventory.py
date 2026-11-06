"""Independent completeness checks against every enumerated input occurrence.
No decoder/semantic support is inferred from a structural reference match.
"""
from pathlib import Path
from collections import Counter,defaultdict
import argparse,hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[3];OWNED=Path(__file__).resolve().parent;OUT=OWNED/'artifacts/corpus-inventory'
parser=argparse.ArgumentParser();parser.add_argument('--read-only',action='store_true');args=parser.parse_args()
def digest(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode()).hexdigest()
def conform(desc,value):
 if 'node' in desc:assert isinstance(value,dict) and value.get('nodeType')==desc['node']
 elif 'object' in desc:
  assert isinstance(value,dict) and desc['object'].keys()==value.keys()
  for key,item in desc['object'].items():conform(item,value[key])
 elif 'array' in desc:
  assert isinstance(value,list) and len(value)==len(desc['array'])
  for item,actual in zip(desc['array'],value):conform(item,actual)
 else:
  actual='null' if value is None else 'bool' if type(value) is bool else 'integer' if type(value) is int else 'string' if isinstance(value,str) else 'number'
  assert desc['scalar']==actual
  if 'value' in desc:assert digest(desc['value'])==digest(value)
def escape(key):return str(key).replace('~','~0').replace('/','~1')
summary=json.loads((OUT/'summary.json').read_text())
manifest=json.loads((OWNED/'corpus-inventory-manifest.json').read_text())
assert summary['counts']==manifest['counts'], 'census manifest count mismatch'
assert summary['sourceBindingCounts']==manifest['sourceBindingCounts'], 'census manifest source-binding count mismatch'
forms={r['formId']:r for r in json.loads((OUT/'forms.json').read_text())}
assert len(forms)==summary['counts']['forms']
expected={};expectedEdges={};indexes={};documents={};formCounts=Counter();kindCounts=Counter();edgeCounts=Counter();functionContexts=Counter();seen=set()
singles={'referencedDeclaration','scope','functionReturnParameters','declaration','function'}
lists={'overloadedDeclarations','baseFunctions','baseModifiers','linearizedBaseContracts','assignments','usedErrors','usedEvents','contractDependencies'}
assert set(summary['identityFields'])==singles|lists|{'exportedSymbols'}
PIN='bc997cd8379d8f3b8af6787f6095f2414adea378'
assert summary['basis']==PIN
subprocess.run(['python3',str(OWNED/'verify-bulk.py')],check=True,cwd=ROOT)
published=subprocess.check_output(['git','ls-tree','-r','--name-only',PIN,'tests/solc',str((OWNED/'fresh').relative_to(ROOT))],cwd=ROOT,text=True).splitlines()
expectedFiles={name for name in published if name.endswith('.ast.json') or ('/fresh/' in name and name.endswith('.raw.json'))}
retained=json.loads((OWNED/'artifacts/h68-bulk/evidence/h68/metadata-compilation.json').read_text())['fixtures']
receiptByPath={}
for receipt in retained:
 for field in ['fixture','rawAst']:
  expectedFiles.add(receipt[field]);receiptByPath[receipt[field]]=receipt
  assert hashlib.sha256((ROOT/receipt[field]).read_bytes()).hexdigest()==receipt[field+'Sha256']
assert {document['path'] for document in summary['documents']}==expectedFiles
attached=defaultdict(list)
for suite in ['', 'fresh-', 'variant-']:
 dataRoot=OWNED if suite!='variant-' else OWNED/'artifacts/h68-bulk'
 caseName=suite+'construct-reader-cases.json' if suite!='variant-' else 'variant-reader-cases.json'
 cases=json.loads((dataRoot/caseName).read_text())['cases']
 for reader in ['', 'composed-']:
  name=reader+suite+'construct-reader-matrix.json' if suite!='variant-' else reader+'variant-reader-matrix.json'
  results=json.loads((dataRoot/name).read_text());assert len(cases)==len(results)
  for case,result in zip(cases,results):
   assert case['nodeType']==result['nodeType'] and case['route']==result['route']
   if 'caseId' in case:assert case['caseId']==result['caseId']
   attached[(case['fixture'],case['fixtureSha256'],case['pointer'])].append({'reader':'default' if not reader else 'composed','suite':suite or 'existing','natural':result['natural'],'unknownRoot':result['unknownRoot']})
observedCounts=Counter()
for document in summary['documents']:
 path=document['path'];raw=(ROOT/path).read_bytes();assert hashlib.sha256(raw).hexdigest()==document['sha256'] and len(raw)==document['bytes']
 assert path not in documents;documents[path]=document
 if path in published:assert hashlib.sha256(subprocess.check_output(['git','show',PIN+':'+path],cwd=ROOT)).hexdigest()==document['sha256']
 for anchor in document.get('anchors',[]):
  if anchor.get('path') is None:assert anchor.get('actualSha256') is None;continue
  source=ROOT/anchor['path']
  if 'inputSha256' in anchor:
   assert hashlib.sha256(source.read_bytes()).hexdigest()==anchor['inputSha256']
   content=json.loads(source.read_text())['sources'][anchor['name']]['content'].encode()
  else:content=source.read_bytes()
  assert hashlib.sha256(content).hexdigest()==anchor['actualSha256']
 try:data=json.loads(raw)
 except (ValueError,RecursionError):assert document['parse']=='refused';continue
 assert document['parse']=='decoded';index=defaultdict(list);indexes[path]=index
 anchors=document['anchors'];header=data.get('header',{}) if isinstance(data,dict) else {}
 if isinstance(data,dict) and isinstance(data.get('sourceAnchors'),list):
  sourceClaims=data['sourceAnchors'];assert len(anchors)==len(sourceClaims)
  for anchor,claim in zip(anchors,sourceClaims):
   assert anchor['claimedSha256']==claim['sourceSha256']
   assert anchor['path']==claim.get('inputFixture',claim.get('source',claim.get('sourceName')))
   assert anchor['name']==claim.get('name',claim.get('sourceName'))
 elif isinstance(data,dict) and isinstance(data.get('sourceUnits'),list):
  units={u['name']:u for u in data['sourceUnits']}
  assert len(anchors)==len(units) and {a['name'] for a in anchors}==units.keys()
  for anchor in anchors:
   assert anchor['claimedSha256']==units[anchor['name']].get('sourceSha256')
   assert (ROOT/anchor['path']).parent==(ROOT/path).parent
 elif header.get('sourceSha256'):
  assert len(anchors)==1 and anchors[0]['claimedSha256']==header['sourceSha256']
  candidates=[(ROOT/path).with_suffix('').with_suffix('.sol')]
  if isinstance(header.get('source'),str):candidates.extend([ROOT/header['source'],(ROOT/path).parent/Path(header['source']).name])
  matching={q for q in candidates if q.is_file() and hashlib.sha256(q.read_bytes()).hexdigest()==header['sourceSha256']}
  if anchors[0]['path'] is None:assert not matching
  else:assert ROOT/anchors[0]['path'] in matching
 elif path in receiptByPath:
  claim=receiptByPath[path];assert len(anchors)==1 and anchors[0]['path']==claim['source'] and anchors[0]['claimedSha256']==claim['sourceSha256']
 else:assert not anchors
 for anchor in anchors:
  if anchor.get('path') is not None:
   committed=subprocess.check_output(['git','show',PIN+':'+anchor['path']],cwd=ROOT)
   assert hashlib.sha256(committed).hexdigest()==hashlib.sha256((ROOT/anchor['path']).read_bytes()).hexdigest()
 requiredBinding='all-hashes-match' if anchors and all(a.get('actualSha256')==a.get('claimedSha256') and a.get('actualSha256') is not None for a in anchors) else 'unavailable-or-mismatch'
 assert document['sourceBinding']==requiredBinding
 def walk(value,pointer='',parent=None,unit=None):
  if isinstance(value,dict):
   if isinstance(value.get('nodeType'),str):
    unit=pointer if value['nodeType']=='SourceUnit' else unit
    expected[(path,pointer)]=(value,parent,unit)
    if type(value.get('id')) is int:index[value['id']].append((pointer,digest(value),unit))
    parent=pointer
   for field,child in value.items():
    location=pointer+'/'+escape(field)
    if field=='function':functionContexts[value.get('nodeType','non-node-child-container')]+=1
    def edge(at,target):expectedEdges[(path,at)]=(field,parent,target)
    if field in singles and (field!='function' or value.get('nodeType') in {'UnaryOperation','BinaryOperation'}):edge(location,child)
    elif field in lists:
     if isinstance(child,list):
      for i,target in enumerate(child):edge(location+'/'+str(i),target)
     else:edge(location,child)
    elif field=='exportedSymbols':
     if isinstance(child,dict):
      for name,targets in child.items():
       if isinstance(targets,list):
        for i,target in enumerate(targets):edge(location+'/'+escape(name)+'/'+str(i),target)
       else:edge(location+'/'+escape(name),targets)
     else:edge(location,child)
    walk(child,location,parent,unit)
  elif isinstance(value,list):
   for i,child in enumerate(value):walk(child,pointer+'/'+str(i),parent,unit)
 walk(data)
for line in (OUT/'nodes.jsonl').open():
 row=json.loads(line);key=(row['fixture'],row['pointer']);assert key not in seen;seen.add(key)
 value,parent,unit=expected[key]
 assert row['fixtureSha256']==documents[key[0]]['sha256'] and row['nodeSha256']==digest(value)
 assert row['parent']==parent and row['unitRoot']==unit and row['nodeType']==value['nodeType']
 assert row['idPresent']==('id' in value) and digest(row['id'])==digest(value.get('id'))
 assert row['scopePresent']==('scope' in value) and digest(row['scope'])==digest(value.get('scope'))
 assert row['src']==value.get('src') and row['name']==value.get('name')
 form=forms[row['formId']]['form'];assert digest(form)==row['formId'] and form['nodeType']==value['nodeType'] and form['fields'].keys()==value.keys()
 for field,desc in form['fields'].items():conform(desc,value[field])
 assert row['observations']==attached.get((key[0],row['fixtureSha256'],key[1]),[])
 observedCounts[row['formId']]+=int(bool(row['observations']))
 formCounts[row['formId']]+=1;kindCounts[value['nodeType']]+=1
assert seen==expected.keys() and len(seen)==summary['counts']['nodes']
for ident,row in forms.items():assert formCounts[ident]==row['occurrences'] and observedCounts[ident]==row['observedOccurrences']
assert sum(count>0 for count in observedCounts.values())==summary['counts']['formsWithSelectedObservations']
seenEdges=set()
for line in (OUT/'edges.jsonl').open():
 row=json.loads(line);key=(row['fixture'],row['pointer']);assert key not in seenEdges;seenEdges.add(key)
 field,parent,target=expectedEdges[key];assert row['field']==field and row['owner']==parent and digest(row['rawTarget'])==digest(target)
 candidates=indexes[key[0]].get(target,[]) if type(target) is int else []
 assert row['targets']==[r[0] for r in candidates]
 if target is None:required='null'
 elif type(target) is not int:required='malformed'
 elif target<0:required='negative-reference-candidate'
 elif 2**31<=target<2**32:required='unsigned-negative-candidate'
 elif not candidates:required='missing-id'
 elif len(candidates)==1:required='unique-node-id'
 elif len({r[1] for r in candidates})==1 and len({r[2] for r in candidates})==len(candidates):required='equivalent-cross-root-candidates'
 else:required='ambiguous-id'
 assert row['status']==required;edgeCounts[required]+=1
assert seenEdges==expectedEdges.keys() and len(seenEdges)==summary['counts']['edges']
assert dict(Counter(d.get('sourceBinding','parse-refused') for d in documents.values()))==summary['sourceBindingCounts']
assert dict(functionContexts)==summary['functionFieldContexts']
assert dict(kindCounts)==summary['nodesByKind'] and dict(edgeCounts)==summary['edgeStatuses']
computedCounts={'documents':len(documents),'nodes':len(seen),'forms':len(forms),'kinds':len(kindCounts),'edges':len(seenEdges),'formsWithSelectedObservations':sum(count>0 for count in observedCounts.values())}
assert computedCounts==manifest['counts'], 'computed census manifest count mismatch'
result={'status':'pass','documents':len(documents),'nodes':len(seen),'forms':len(forms),'identityFields':summary['identityFields'],'edges':len(seenEdges),'boundary':'All enumerated occurrences/field schemas/explicit reference slots checked;not source authenticity,lexical/overload adequacy or semantic preservation.'}
if not args.read_only:(OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
