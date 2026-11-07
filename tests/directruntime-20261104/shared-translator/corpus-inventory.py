"""Lossless occurrence/identity census plus explicitly bounded immediate-field forms.
This observes compiler JSON; it never translates ASTs or infers semantic support.
Generated data stays outside Git. Every document is a separate identity world.
"""
from pathlib import Path
from collections import Counter, defaultdict
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[3];OWNED=Path(__file__).resolve().parent
OUT=OWNED/'artifacts/corpus-inventory';BULK=OWNED/'artifacts/h68-bulk'
PIN='bc997cd8379d8f3b8af6787f6095f2414adea378'
SINGLES={'referencedDeclaration','scope','functionReturnParameters','declaration','function'}
LISTS={'overloadedDeclarations','baseFunctions','baseModifiers','linearizedBaseContracts','assignments','usedErrors','usedEvents','contractDependencies'}
VALUES={'operator','kind','visibility','stateMutability','storageLocation','mutability','contractKind','language','stateVariable','virtual','constant','immutable','isInlineArray','prefix','tryCall','isConstant','implemented'}
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=True)
def digest(value):return hashlib.sha256(encoded(value).encode()).hexdigest()
def ptr(key):return str(key).replace('~','~0').replace('/','~1')
def shape(value,field=None):
 if isinstance(value,dict):
  if isinstance(value.get('nodeType'),str):return {'node':value['nodeType']}
  return {'object':{k:shape(v,k) for k,v in sorted(value.items())}}
 if isinstance(value,list):return {'array':[shape(v,field) for v in value]}
 kind='null' if value is None else 'bool' if type(value) is bool else 'integer' if type(value) is int else 'string' if isinstance(value,str) else 'number'
 out={'scalar':kind}
 if field in VALUES or type(value) is bool:out['value']=value
 return out
def form(node):return {'nodeType':node['nodeType'],'fields':{k:shape(v,k) for k,v in sorted(node.items())}}
def sources(path,data):
 anchors=[];header=data.get('header',{}) if isinstance(data,dict) else {}
 if isinstance(data,dict) and isinstance(data.get('sourceAnchors'),list):
  for row in data['sourceAnchors']:
   if 'inputFixture' in row:
    inp=ROOT/row['inputFixture'];name=row.get('name',row.get('sourceName'))
    content=json.loads(inp.read_text())['sources'][name]['content'].encode()
    anchors.append({'name':name,'path':str(inp.relative_to(ROOT)),'inputSha256':sha(inp),'claimedSha256':row['sourceSha256'],'actualSha256':hashlib.sha256(content).hexdigest()})
   else:
    source=ROOT/row.get('source',row.get('sourceName',''))
    anchors.append({'name':row.get('name',row.get('sourceName')),'path':str(source.relative_to(ROOT)),'claimedSha256':row['sourceSha256'],'actualSha256':sha(source) if source.is_file() else None})
 elif isinstance(data,dict) and isinstance(data.get('sourceUnits'),list):
  for inp in sorted(path.parent.glob('*.input.json')):
   texts=json.loads(inp.read_text()).get('sources',{})
   units=data['sourceUnits']
   if all(u.get('name') in texts for u in units):
    anchors=[{'name':u['name'],'path':str(inp.relative_to(ROOT)),'inputSha256':sha(inp),'claimedSha256':u.get('sourceSha256'),'actualSha256':hashlib.sha256(texts[u['name']]['content'].encode()).hexdigest()} for u in units]
    break
 elif header.get('sourceSha256'):
  named=header.get('source');candidates=[path.with_suffix('').with_suffix('.sol')]
  if isinstance(named,str):candidates.extend([ROOT/named,path.parent/Path(named).name])
  matching=next((q for q in candidates if q.is_file() and sha(q)==header['sourceSha256']),None)
  anchors=[{'name':named,'path':str(matching.relative_to(ROOT)) if matching and matching.is_relative_to(ROOT) else None,'claimedSha256':header['sourceSha256'],'actualSha256':sha(matching) if matching else None}]
 return anchors
def resolve(target,index):
 matches=index.get(target,[]) if type(target) is int else []
 if target is None:status='null'
 elif type(target) is not int:status='malformed'
 elif target<0:status='negative-reference-candidate'
 elif 2**31<=target<2**32:status='unsigned-negative-candidate'
 elif not matches:status='missing-id'
 elif len(matches)==1:status='unique-node-id'
 elif len({x['nodeSha256'] for x in matches})==1 and len({x['unitRoot'] for x in matches})==len(matches):status='equivalent-cross-root-candidates'
 else:status='ambiguous-id'
 return status,[x['pointer'] for x in matches]
def inputs():
 files={path:('existing-corpus',None) for path in sorted((ROOT/'tests/solc').rglob('*.ast.json'))}
 fresh=sorted((OWNED/'fresh').glob('*.raw.json'))
 published=subprocess.check_output(['git','ls-tree','-r','--name-only',PIN,'tests/solc',str((OWNED/'fresh').relative_to(ROOT))],cwd=ROOT,text=True).splitlines()
 expected={name for name in published if name.endswith('.ast.json') or ('/fresh/' in name and name.endswith('.raw.json'))}
 assert expected=={str(path.relative_to(ROOT)) for path in list(files)+fresh},'source corpus file set differs from recorded commit'
 for row in json.loads((BULK/'evidence/h68/metadata-compilation.json').read_text())['fixtures']:
  for field in ['fixture','rawAst']:
   path=ROOT/row[field];assert sha(path)==row[field+'Sha256']
   files[path]=('retained-h68-normalized' if field=='fixture' else 'retained-h68-raw',row)
 for path in fresh:files[path]=('retained-h41-raw',None)
 return sorted(files.items())
def check_observation_identity(case,result):
 assert result['nodeType']==case['nodeType'] and result['route']==case['route'],'observation kind/route changed'
 if 'caseId' in case:assert result.get('caseId')==case['caseId'],'observation case identity changed'
def main():
 OUT.mkdir(exist_ok=True)
 subprocess.run(['python3',str(OWNED/'verify-bulk.py')],check=True,cwd=ROOT)
 forms={};documents=[];nodeCounts=Counter();edgeCounts=Counter();fieldCounts=Counter();candidateFields=Counter();functionContexts=Counter();observations=defaultdict(list)
 for prefix in ['', 'fresh-','variant-']:
  cases=OWNED/(prefix+'construct-reader-cases.json') if prefix!='variant-' else BULK/'variant-reader-cases.json'
  if not cases.is_file():continue
  rows=json.loads(cases.read_text())['cases']
  for read in ['', 'composed-']:
   matrix=OWNED/(read+prefix+'construct-reader-matrix.json') if prefix!='variant-' else BULK/(read+'variant-reader-matrix.json')
   results=json.loads(matrix.read_text());assert len(rows)==len(results)
   for case,result in zip(rows,results):
    check_observation_identity(case,result)
    observations[(case['fixture'],case['fixtureSha256'],case['pointer'])].append({'reader':'default' if not read else 'composed','suite':prefix or 'existing','natural':result['natural'],'unknownRoot':result['unknownRoot']})
 with (OUT/'nodes.jsonl').open('w') as nodesFile,(OUT/'edges.jsonl').open('w') as edgesFile:
  for (path,(origin,receipt)) in inputs():
   relative=str(path.relative_to(ROOT));fileSha=sha(path)
   if origin in {'existing-corpus','retained-h41-raw'}:
    published=subprocess.check_output(['git','show',PIN+':'+relative],cwd=ROOT)
    assert hashlib.sha256(published).hexdigest()==fileSha,'input differs from recorded source commit: '+relative
   document={'path':relative,'sha256':fileSha,'bytes':path.stat().st_size,'origin':origin}
   try:data=json.loads(path.read_text())
   except (ValueError,RecursionError) as error:
    document.update(parse='refused',diagnostic=str(error),nodes=0,edges=0);documents.append(document);continue
   document.update(parse='decoded',anchors=sources(path,data),compilerClaim=(receipt or {}).get('compiler',data.get('compiler',data.get('header',{})) if isinstance(data,dict) else {}))
   if receipt and not document['anchors']:
    source=ROOT/receipt['source'];document['anchors']=[{'path':receipt['source'],'claimedSha256':receipt['sourceSha256'],'actualSha256':sha(source)}]
   index=defaultdict(list);nodeRows=[];edgeRows=[]
   def walk(value,pointer='',parent=None,unit=None):
    if isinstance(value,dict):
     if isinstance(value.get('nodeType'),str):
      kind=value['nodeType'];unit=pointer if kind=='SourceUnit' else unit
      signature=form(value);formId=digest(signature)
      entry=forms.setdefault(formId,{'formId':formId,'form':signature,'occurrences':0,'observedOccurrences':0,'witness':{'fixture':relative,'fixtureSha256':fileSha,'pointer':pointer}});entry['occurrences']+=1
      row={'fixture':relative,'fixtureSha256':fileSha,'pointer':pointer,'nodeType':kind,'formId':formId,'nodeSha256':digest(value),'parent':parent,'unitRoot':unit,'id':value.get('id'),'idPresent':'id' in value,'src':value.get('src'),'name':value.get('name'),'scopePresent':'scope' in value,'scope':value.get('scope'),'observations':observations.get((relative,fileSha,pointer),[])}
      entry['observedOccurrences']+=int(bool(row['observations']))
      nodeRows.append(row);nodeCounts[kind]+=1
      if type(value.get('id')) is int:index[value['id']].append(row)
      parent=pointer
     for key,child in value.items():
      location=pointer+'/'+ptr(key);fieldCounts[key]+=1
      if key=='function':functionContexts[value.get('nodeType','non-node-child-container')]+=1
      if key in SINGLES|LISTS|{'exportedSymbols','externalReferences','internalFunctionIDs'} or any(word in key.lower() for word in ['declaration','scope','ids','identifier']):candidateFields[key]+=1
      def edge(at,target):edgeRows.append({'fixture':relative,'pointer':at,'field':key,'owner':parent,'rawTarget':target})
      if key in SINGLES and (key!='function' or value.get('nodeType') in {'UnaryOperation','BinaryOperation'}):edge(location,child)
      elif key in LISTS:
       if isinstance(child,list):
        for i,target in enumerate(child):edge(location+'/'+str(i),target)
       else:edge(location,child)
      elif key=='exportedSymbols':
       if isinstance(child,dict):
        for name,targets in child.items():
         if isinstance(targets,list):
          for i,target in enumerate(targets):edge(location+'/'+ptr(name)+'/'+str(i),target)
         else:edge(location+'/'+ptr(name),targets)
       else:edge(location,child)
      walk(child,location,parent,unit)
    elif isinstance(value,list):
     for i,child in enumerate(value):walk(child,pointer+'/'+str(i),parent,unit)
   walk(data)
   for row in edgeRows:
    status,targets=resolve(row['rawTarget'],index)
    row.update(status=status,targets=targets);edgeCounts[status]+=1
    edgesFile.write(encoded(row)+'\n')
   for row in nodeRows:nodesFile.write(encoded(row)+'\n')
   duplicates=[{'id':ident,'pointers':[x['pointer'] for x in rows]} for ident,rows in index.items() if len(rows)>1]
   document['sourceBinding']='all-hashes-match' if document['anchors'] and all(a.get('actualSha256')==a.get('claimedSha256') and a.get('actualSha256') is not None for a in document['anchors']) else 'unavailable-or-mismatch'
   document.update(nodes=len(nodeRows),edges=len(edgeRows),duplicateIds=duplicates);documents.append(document)
 coverage=json.loads((OWNED/'coverage-inventory.json').read_text());catalog={r['nodeType']:r for r in coverage['constructs']+coverage['yulConstructs']}
 for row in forms.values():
  entry=catalog.get(row['form']['nodeType'],{})
  row.update(owners=entry.get('owners',entry.get('owner','owner mapping absent')),admission='not independently executed for this structural form',proofClosure='no source-preservation proof inferred',semanticSupport='unknown at form level',backendGap=entry.get('backendGap',entry.get('backend','not established')))
 (OUT/'forms.json').write_text(json.dumps(list(forms.values()),indent=2)+'\n')
 summary={'basis':PIN,'documents':documents,'counts':{'documents':len(documents),'nodes':sum(nodeCounts.values()),'forms':len(forms),'kinds':len(nodeCounts),'edges':sum(edgeCounts.values()),'formsWithSelectedObservations':sum(row['observedOccurrences']>0 for row in forms.values())},'nodesByKind':dict(sorted(nodeCounts.items())),'edgeStatuses':dict(sorted(edgeCounts.items())),'sourceBindingCounts':dict(Counter(d.get('sourceBinding','parse-refused') for d in documents)),'identityFieldContexts':{'function':['UnaryOperation','BinaryOperation']},'functionFieldContexts':dict(functionContexts),'candidateKeyPolicy':'Heuristic includes all object-envelope keys;source filenames can be false positives. Listed reference-slot policy is separate.','unclassifiedIdentityCandidates':sorted(set(candidateFields)-SINGLES-LISTS-{'exportedSymbols','id'}),'opaqueIdentityContainers':{'function':'Only Unary/BinaryOperation scalar function fields are graph edges;UsingFor child containers are traversed via nested referencedDeclaration,not interpreted as scalar aliases','externalReferences':'Container inventoried;nested declaration fields resolved structurally,assembly capture/offset semantics unproved','internalFunctionIDs':'Opaque compiler declaration/backend-index map;no key/value source-to-backend identity interpretation','typeIdentifier':'Opaque nominal identity string;not interpreted as a graph edge'},'identityFields':sorted(SINGLES|LISTS|{'exportedSymbols'}),'candidateIdentityKeys':dict(sorted(candidateFields.items())),'allFieldKeys':dict(sorted(fieldCounts.items())),'unobservedCatalogKinds':sorted(set(catalog)-set(nodeCounts)),'boundary':'Exhaustive occurrence accounting for the enumerated finite corpus only. Forms are immediate field schemas,ordered child slots and selected scalar discriminants,not exhaustive semantic forms. Identity edges use explicit listed fields;candidate keys remain inventoried. Reference resolution is structural,not lexical/type/overload adequacy. Retained compiler output/header/source hashes do not prove source preservation. Unobserved or untested forms remain unknown.'}
 (OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({'counts':summary['counts'],'edgeStatuses':summary['edgeStatuses'],'unobservedCatalogKinds':summary['unobservedCatalogKinds']}))
if __name__=='__main__':main()
