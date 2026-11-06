"""Bind every frozen observed-subvariant row to its inventoried fixture identity.
Compiler headers in old fixtures are claims, not authenticated compiler output.
"""
from pathlib import Path
import collections, hashlib, json
owned=Path(__file__).resolve().parent;root=owned.parents[2]
bulk=owned/'artifacts/h68-bulk'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def select(value,pointer):
 for part in pointer.split('/')[1:]:
  key=part.replace('~1','/').replace('~0','~');value=value[int(key)] if isinstance(value,list) else value[key]
 return value
def observedFields(n,parent,key):
 # Independently check the eight inventoried field schemas against the witness.
 ty=lambda x:x.get('typeDescriptions',{}).get('typeString') if isinstance(x,dict) else None
 kind=n['nodeType']
 if kind=='VariableDeclaration':return dict(location=n.get('storageLocation'),state=n.get('stateVariable'),mutability=n.get('mutability'),typeNode=(n.get('typeName') or {}).get('nodeType'),type=ty(n))
 if kind=='ElementaryTypeName':return dict(name=n.get('name'),stateMutability=n.get('stateMutability'))
 if kind=='FunctionTypeName':return dict(visibility=n.get('visibility'),stateMutability=n.get('stateMutability'))
 if kind=='Literal':return dict(kind=n.get('kind'),type=ty(n),unit=n.get('subdenomination'))
 if kind=='UnaryOperation':return dict(operator=n.get('operator'),prefix=n.get('prefix'),resolvedFunctionPresent='function' in n)
 if kind=='BinaryOperation':return dict(operator=n.get('operator'),commonType=(n.get('commonType') or {}).get('typeString'),resolvedFunctionPresent='function' in n)
 if kind=='TupleExpression':return dict(inlineArray=n.get('isInlineArray'),arity=len(n.get('components',[])),holes=any(x is None for x in n.get('components',[])),parentKind=parent,parentKey=key)
 assert kind=='FunctionCall'
 callee=n.get('expression',{});reference=callee.get('referencedDeclaration')
 return dict(callKind=n.get('kind'),calleeKind=callee.get('nodeType'),calleeName=callee.get('name',callee.get('memberName')),referenceSign='builtin-negative' if isinstance(reference,int) and reference<0 else 'declaration-nonnegative' if isinstance(reference,int) else 'missing',namedArguments=bool(n.get('names')))
def context(value,pointer):
 parent=key=None
 for part in pointer.split('/')[1:]:
  token=part.replace('~1','/').replace('~0','~')
  if isinstance(value,dict):parent=value.get('nodeType');key=token;value=value[token]
  else:value=value[int(token)]
 return parent,key
inventory=json.loads((bulk/'fixture-variants.json').read_text())
cases=json.loads((bulk/'variant-reader-cases.json').read_text())
matrices=[json.loads((bulk/name).read_text()) for name in ['variant-reader-matrix.json','composed-variant-reader-matrix.json']]
assert cases['basis']==inventory['basis']=='4095d848297d87e374b4f069692511cfe4a36cf7'
assert len(cases['cases'])==len(inventory['variants'])==inventory['variantCount']==806
assert all(len(m)==806 for m in matrices)
seen=set();changes=[];fixtureCache={}
for index,(case,variant) in enumerate(zip(cases['cases'],inventory['variants'])):
 assert case['variant']==variant['variant']
 key=hashlib.sha256(json.dumps(case['variant'],sort_keys=True,separators=(',',':')).encode()).hexdigest()
 assert case['caseId']==key and key not in seen;seen.add(key)
 witness=variant['witnesses'][0]
 assert all(case[k]==v for k,v in witness.items())
 path=root/case['fixture']
 if path not in fixtureCache:fixtureCache[path]=(sha(path),json.loads(path.read_text()))
 digest,fixture=fixtureCache[path];assert digest==case['fixtureSha256']
 node=select(fixture,case['pointer'])
 assert node['nodeType']==case['nodeType']==case['variant']['nodeType']
 assert node.get('id')==case['nodeId'] and node.get('src')==case['src']
 assert fixture.get('header',{}).get('solcVersion')==case['compilerVersion']
 assert observedFields(node,*context(fixture,case['pointer']))==case['variant']['fields'], 'variant mislabeled'
 before,after=[m[index] for m in matrices]
 for row in [before,after]:
  assert row['caseId']==key and row['nodeType']==case['nodeType'] and row['route']==case['route']
  if case['route']=='none':assert row['natural']=={'status':'not-standalone'} and row['unknownRoot'] is None
  else:assert row['natural']['status'] in {'decoded','refused'} and row['unknownRoot']['status']=='refused'
 assert before['producerExpression']==after['producerExpression']
 if before['natural']!=after['natural']:changes.append({'caseId':key,'variant':case['variant'],'before':before['natural'],'composed':after['natural'],'fixture':case['fixture'],'pointer':case['pointer']})
callableCounts=[sum(r['unknownRoot'] is not None and r['unknownRoot']['status']=='refused' for r in matrix) for matrix in matrices]
assert callableCounts==[553,553] and sum(case['route']!='none' for case in cases['cases'])==553
summary={'basis':cases['basis'],'cases':806,'selectedFieldKinds':inventory['byKind'],'fixtureCount':len(fixtureCache),'default':dict(collections.Counter(r['natural']['status'] for r in matrices[0])),'composed':dict(collections.Counter(r['natural']['status'] for r in matrices[1])),'unknownRootRefusalsEachReader':callableCounts[0],'changedWitnesses':len(changes),'changes':changes,'inputs':{name:sha(bulk/name) for name in ['fixture-variants.json','variant-reader-cases.json','variant-reader-matrix.json','composed-variant-reader-matrix.json']},'boundary':'All806 observed selected-field subvariants have one exact fixture-anchored standalone observation per reader and unknown-root controls where callable.253 declarations lack standalone entry and are explicit. Corpus may contain intentional mutations; compiler header claims are not fresh compiler provenance. Decoding/printing/refusal is not intrinsic elaboration,proof closure,source preservation or backend support. No exhaustive syntax-form claim.'}
(bulk/'variant-reader-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['cases','fixtureCount','default','composed','unknownRootRefusalsEachReader','changedWitnesses']}))
