"""Existing source-anchored compiler-fixture census; not an execution proof."""
from pathlib import Path
import json,hashlib,collections
root=Path(__file__).resolve().parents[3]
owned=Path(__file__).resolve().parent
inventory=json.loads((owned/'coverage-inventory.json').read_text())
kinds={x['nodeType'] for x in inventory['constructs']}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def digest(s):return hashlib.sha256(s.encode()).hexdigest()
fixtures=[]
for path in sorted((root/'tests/solc').rglob('*.ast.json')):
    try:data=json.loads(path.read_text())
    except (ValueError,OSError):continue
    header=data.get('header',{})
    anchors=[]
    if header.get('provenanceVersion')==2:
        units=data.get('sourceUnits',[])
        for inp in sorted(path.parent.glob('*.input.json')):
            try:inputs=json.loads(inp.read_text()).get('sources',{})
            except (ValueError,OSError):continue
            if units and all(u.get('name') in inputs and digest(inputs[u['name']]['content'])==u.get('sourceSha256') for u in units):
                anchors=[{'sourceName':u['name'],'sourceId':u.get('id'),'sourceSha256':u['sourceSha256'],'inputFixture':str(inp.relative_to(root)),'inputSha256':sha(inp)} for u in units]
                break
    else:
        candidates=[path.with_suffix('').with_suffix('.sol')]
        named=header.get('source')
        if isinstance(named,str):
            q=Path(named)
            if not q.is_absolute():candidates.extend([root/q,path.parent/q.name])
        for q in candidates:
            if q.is_file() and sha(q)==header.get('sourceSha256'):
                anchors=[{'sourceName':str(q.relative_to(root)),'sourceSha256':sha(q)}]
                break
    examples={}
    def walk(value,pointer='',function=None,contract=None):
        if isinstance(value,dict):
            kind=value.get('nodeType')
            if kind=='FunctionDefinition':function={'id':value.get('id'),'name':value.get('name'),'src':value.get('src'),'line':value.get('line')}
            if kind=='ContractDefinition':contract={'id':value.get('id'),'name':value.get('name')}
            if kind in kinds and kind not in examples:
                examples[kind]={'pointer':pointer,'function':function,'contract':contract,'nodeId':value.get('id'),'src':value.get('src'),'line':value.get('line')}
            for key,child in value.items():walk(child,pointer+'/'+key.replace('~','~0').replace('/','~1'),function,contract)
        elif isinstance(value,list):
            for i,child in enumerate(value):walk(child,pointer+'/'+str(i),function,contract)
    walk(data)
    fixtures.append({'fixture':str(path.relative_to(root)),'fixtureSha256':sha(path),'compilerVersion':header.get('solcVersion'),'compilerSha256':header.get('compilerSha256'),'provenanceVersion':header.get('provenanceVersion'),'anchors':anchors,'examples':examples})
remaining=kinds-{'Throw'};selected=[]
while remaining:
    candidates=[f for f in fixtures if f['anchors'] and f not in selected]
    if not candidates:break
    best=max(candidates,key=lambda f:len(set(f['examples'])&remaining))
    if not set(best['examples'])&remaining:break
    selected.append(best);remaining-=set(best['examples'])
rows=[]
for kind in sorted(kinds):
    candidates=[{'fixture':f['fixture'],'fixtureSha256':f['fixtureSha256'],'compilerVersion':f['compilerVersion'],'compilerSha256':f['compilerSha256'],'anchors':f['anchors'],**f['examples'][kind]} for f in selected if kind in f['examples']]
    rows.append({'nodeType':kind,'existingSourceWitnesses':candidates[:2],
      'status':'legacy-only; modern compiler/source negative control required' if kind=='Throw' else 'source-anchored fixture occurrence' if candidates else 'source anchor pending',
      'boundary':'Source/header hashes and AST location only. Fixture regeneration, per-construct admission, intrinsic closure and backend execution are separate gates.'})
result={'schemaVersion':1,'basis':'dc2718096308da55e57e713a4d3b37aec4d47606','publishedProducerApis':'89373e34cdfd6bb5db7054b1c204d01edffc5fa7','counts':{'knownKinds':len(kinds),'existingFixtures':len(fixtures),'sourceAnchoredFixtures':sum(bool(f['anchors']) for f in fixtures),'selectedFixtures':len(selected),'modernKindsWithAnchoredWitnesses':len(kinds-{'Throw'})-len(remaining)},'missingModernKinds':sorted(remaining),'constructs':rows,
 'selectedFixturePaths':[f['fixture'] for f in selected],
 'boundary':'Existing test fixtures may include deliberate mutations. Matching source/header hashes do not authenticate compiler execution or prove AST-to-source equivalence.'}
(owned/'fixture-census.json').write_text(json.dumps(result,indent=2)+'\n')
assert not remaining, remaining
print(json.dumps(result['counts'],sort_keys=True))
