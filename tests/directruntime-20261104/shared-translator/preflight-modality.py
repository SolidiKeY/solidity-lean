"""Bind paired modal observations to exact source, AST and compiler bytes."""
from pathlib import Path
from collections import Counter
import hashlib,json
owned=Path(__file__).resolve().parent;root=owned.parents[2]
bulk=owned/'artifacts/h68-bulk'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipt=json.loads((bulk/'evidence/h68/modality-compilation.json').read_text())
assert sha(root/receipt['source'])==receipt['sourceSha256']
assert sha(root/receipt['fixture'])==receipt['fixtureSha256']
assert sha(root/receipt['rawAst'])==receipt['rawAstSha256']
binary=Path('/workspace/.setup/soljson/soljson-v0.8.34+commit.80d5c536.js')
assert sha(binary)==receipt['compiler']['sha256']=='c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8'
assert receipt['compiler']['version']=='0.8.34+commit.80d5c536.Emscripten.clang'
fixture=json.loads((root/receipt['fixture']).read_text());source=(root/receipt['source']).read_bytes()
contract=next(n for n in fixture['ast']['nodes'] if n.get('nodeType')=='ContractDefinition')
functions={n['name']:n for n in contract['nodes'] if n.get('nodeType')=='FunctionDefinition'}
raw=json.loads((root/receipt['rawAst']).read_text());rawContract=next(n for n in raw['nodes'] if n.get('nodeType')=='ContractDefinition')
rawFunctions={n['name']:n for n in rawContract['nodes'] if n.get('nodeType')=='FunctionDefinition'}
assert functions.keys()==rawFunctions.keys() and all(n['id']==rawFunctions[name]['id'] and n['src']==rawFunctions[name]['src'] for name,n in functions.items())
observations=json.loads((owned/'modality-observations.json').read_text());assert len(functions)==len(observations)==6
seen=set();rows=[]
def span(src):
 start,length,unit=map(int,src.split(':'));assert unit==0 and start>=0 and length>=0 and start+length<=len(source)
 return source[start:start+length]
for observed in observations:
 row=observed['checker'];name=row['function'];node=functions[name]
 assert name not in seen;seen.add(name)
 assert row['sourceId']==node['id'] and node['visibility']=='public'
 assert ('function '+name).encode() in span(node['src'])
 box=name.endswith('Box');tag='box' if box else 'diamond'
 doc=node.get('documentation',{});doc=doc.get('text','') if isinstance(doc,dict) else doc
 assert ('@custom:key box' in doc)==box and row['tag']==tag
 assert row['reading']=='solc' and row['verification']=='direct'
 if row['status']=='refuted':assert isinstance(row['counterexample'],dict)
 rows.append({'name':name,'nodeId':node['id'],'src':node['src'],'line':node.get('line'),'tag':tag,'finiteHalt':observed['finiteHalt'],'trustedCheckerStatus':row['status'],'bodySha256':hashlib.sha256(span(node['body']['src'])).hexdigest()})
assert seen==set(functions)
pairs=[]
for stem in ['normal','revert','panic']:
 box=functions[stem+'Box'];diamond=functions[stem+'Diamond'];assert span(box['body']['src'])==span(diamond['body']['src'])
 pairs.append({'box':box['name'],'diamond':diamond['name'],'bodyBytesIdentical':True})
result={'source':receipt['source'],'sourceSha256':receipt['sourceSha256'],'rawAst':receipt['rawAst'],'rawAstSha256':receipt['rawAstSha256'],'fixture':receipt['fixture'],'fixtureSha256':receipt['fixtureSha256'],'compiler':receipt['compiler'],'observationsSha256':sha(owned/'modality-observations.json'),'cases':rows,'pairs':pairs,'checkerCounts':dict(Counter(r['trustedCheckerStatus'] for r in rows)),'boundary':'Six source-identified paired body-byte controls,finite initial-state runs and trusted public checker observations. This validates provenance and regression intent,not compiler/source preservation,Lean proof terms or native/WASM closure.'}
(bulk/'modality-ledger.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS six source/AST identities, three byte-identical body pairs, exact compiler binary and observed modal tags; no source/native proof claim.')
