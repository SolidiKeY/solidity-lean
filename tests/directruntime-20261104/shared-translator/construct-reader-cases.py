"""Source-anchored standalone reader controls; no new AST translator or IR."""
from pathlib import Path
import json,hashlib,collections
owned=Path(__file__).resolve().parent;root=owned.parents[2]
expressions=set('Assignment BinaryOperation Conditional ElementaryTypeNameExpression FunctionCall FunctionCallOptions Identifier IndexAccess IndexRangeAccess Literal MemberAccess NewExpression TupleExpression UnaryOperation'.split())
statements=set('Block UncheckedBlock Return IfStatement VariableDeclarationStatement WhileStatement ForStatement Break Continue ExpressionStatement DoWhileStatement EmitStatement RevertStatement TryStatement PlaceholderStatement InlineAssembly'.split())
types=set('ElementaryTypeName ArrayTypeName Mapping UserDefinedTypeName FunctionTypeName'.split())
def select(value,pointer):
 for part in pointer.split('/')[1:]:
  key=part.replace('~1','/').replace('~0','~');value=value[int(key)] if isinstance(value,list) else value[key]
 return value
cases=[]
for row in json.loads((owned/'fixture-census.json').read_text())['constructs']:
 kind=row['nodeType']
 if kind=='Throw':continue
 witness=row['existingSourceWitnesses'][0];path=root/witness['fixture']
 assert hashlib.sha256(path.read_bytes()).hexdigest()==witness['fixtureSha256']
 node=select(json.loads(path.read_text()),witness['pointer']);assert node['nodeType']==kind
 route='expression' if kind in expressions else 'statements' if kind in statements else 'typeName' if kind in types else 'function' if kind=='FunctionDefinition' else 'contract' if kind=='ContractDefinition' else 'none'
 cases.append({'nodeType':kind,'route':route,**witness})
assert len(cases)==57
out={'boundary':'Standalone Shared decoder/admission-root observations only. Some syntax kinds have no standalone reader entrypoint. Existing fixture ASTs may contain deliberate mutations; anchors are not authenticated compilation. Neither intrinsic/source proof nor backend support follows.','cases':cases}
(owned/'construct-reader-cases.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'cases':len(cases),'routes':dict(collections.Counter(x['route'] for x in cases))}))

# Fresh raw compiler ASTs provide a separate, actually regenerated observation set.
known={row['nodeType'] for row in json.loads((owned/'fixture-census.json').read_text())['constructs']}-{'Throw'}
fresh={};unexpected=set()
for path in sorted((owned/'fresh').glob('*.raw.json')):
 data=json.loads(path.read_text());fixtureHash=hashlib.sha256(path.read_bytes()).hexdigest()
 for unit,ast in data['compilerAsts'].items():
  anchor=next(x for x in data['sourceAnchors'] if x['name']==unit)
  if 'source' in anchor:content=(root/anchor['source']).read_bytes()
  else:content=json.loads((root/anchor['inputFixture']).read_text())['sources'][unit]['content'].encode()
  assert hashlib.sha256(content).hexdigest()==anchor['sourceSha256']
  def location(node):
   src=node.get('src');line=None
   if isinstance(src,str):line=content[:int(src.split(':')[0])].count(b'\n')+1
   return {'src':src,'line':line}
  def walk(node,pointer,function=None,contract=None):
   if isinstance(node,dict):
    kind=node.get('nodeType')
    if kind and kind not in known and not kind.startswith('Yul'):unexpected.add(kind)
    if kind=='FunctionDefinition':function={'id':node.get('id'),'name':node.get('name'),**location(node)}
    if kind=='ContractDefinition':contract={'id':node.get('id'),'name':node.get('name')}
    if kind in known and kind not in fresh:
     route='expression' if kind in expressions else 'statements' if kind in statements else 'typeName' if kind in types else 'function' if kind=='FunctionDefinition' else 'contract' if kind=='ContractDefinition' else 'none'
     fresh[kind]={'nodeType':kind,'route':route,'fixture':str(path.relative_to(root)),'fixtureSha256':fixtureHash,'pointer':pointer,'compilerVersion':data['compiler']['version'],'compilerSha256':data['compiler']['sha256'],'anchors':data['sourceAnchors'],'unit':unit,'function':function,'contract':contract,'nodeId':node.get('id'),**location(node)}
    for key,value in node.items():walk(value,pointer+'/'+key.replace('~','~0').replace('/','~1'),function,contract)
   elif isinstance(node,list):
    for i,value in enumerate(node):walk(value,pointer+'/'+str(i),function,contract)
  walk(ast,'/compilerAsts/'+unit.replace('~','~0').replace('/','~1'))
assert not unexpected,unexpected
assert set(fresh)==known,(known-set(fresh),set(fresh)-known)
(owned/'fresh-construct-reader-cases.json').write_text(json.dumps({'boundary':'Fresh exact-pinned compiler executions, unmodified raw ASTs. Reader outcome is not intrinsic elaboration, proof closure or backend execution.','cases':[fresh[k] for k in sorted(fresh)]},indent=2)+'\n')
print(json.dumps({'freshCases':len(fresh),'routes':dict(collections.Counter(x['route'] for x in fresh.values()))}))
