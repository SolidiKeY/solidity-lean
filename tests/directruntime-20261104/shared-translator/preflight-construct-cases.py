"""Validate frozen source/fixture identities independently of reader observations."""
from pathlib import Path
import hashlib,json,collections
owned=Path(__file__).resolve().parent;root=owned.parents[2]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def select(value,pointer):
 for part in pointer.split('/')[1:]:
  key=part.replace('~1','/').replace('~0','~');value=value[int(key)] if isinstance(value,list) else value[key]
 return value
expected={x['nodeType'] for x in json.loads((owned/'fixture-census.json').read_text())['constructs']}-{'Throw'}
for prefix in ['', 'fresh-']:
 cases=json.loads((owned/(prefix+'construct-reader-cases.json')).read_text())['cases']
 matrix=json.loads((owned/(prefix+'construct-reader-matrix.json')).read_text())
 assert len(cases)==len(matrix)==57 and {x['nodeType'] for x in cases}==expected
 assert {x['nodeType'] for x in matrix}==expected
 for row in cases:
  path=root/row['fixture'];assert sha(path)==row['fixtureSha256']
  node=select(json.loads(path.read_text()),row['pointer'])
  assert node['nodeType']==row['nodeType'] and node.get('id')==row['nodeId'] and node.get('src')==row['src']
  for anchor in row['anchors']:
   if 'inputFixture' in anchor:
    inp=root/anchor['inputFixture'];assert sha(inp)==anchor['inputSha256']
    content=json.loads(inp.read_text())['sources'][anchor.get('name',anchor.get('sourceName'))]['content'].encode()
   else:content=(root/anchor.get('source',anchor.get('sourceName'))).read_bytes()
   assert hashlib.sha256(content).hexdigest()==anchor['sourceSha256']
 print(json.dumps({'suite':prefix or 'existing','kinds':len(cases),'outcomes':dict(collections.Counter(x['natural']['status'] for x in matrix))}))
receipts=json.loads((owned/'evidence/h41/fresh-compilation.json').read_text())['fixtures']
assert len(receipts)==8
for receipt in receipts:
 path=root/receipt['output'];assert sha(path)==receipt['outputSha256']
 data=json.loads(path.read_text());assert data['compiler']==receipt['compiler'] and data['sourceAnchors']==receipt['sourceAnchors']
for path,expectedSha in [(owned/'artifacts/compiler/soljson-v0.8.38+commit.1835d247.js','6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390'),(Path('/workspace/.setup/soljson/soljson-v0.8.34+commit.80d5c536.js'),'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8')]:assert sha(path)==expectedSha
print('PASS 114 source-witness identities, eight fresh compiler-output hashes and two exact compiler binary pins; no semantic/backend proof claim.')
