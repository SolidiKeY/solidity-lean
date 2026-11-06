"""Independently bind H68 fixture metadata to compiler and prior normalized bytes."""
from pathlib import Path
import collections, hashlib, json, subprocess
owned=Path(__file__).resolve().parent;root=owned.parents[2]
bulk=owned/'artifacts/h68-bulk'
pin='4095d848297d87e374b4f069692511cfe4a36cf7'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def walk(value):
 if isinstance(value,dict):
  yield value
  for x in value.values():yield from walk(x)
 elif isinstance(value,list):
  for x in value:yield from walk(x)
def strip(value):
 if isinstance(value,dict):return {k:strip(v) for k,v in value.items() if k not in {'typeIdentifier','tryCall'}}
 if isinstance(value,list):return [strip(v) for v in value]
 return value
receipts=json.loads((bulk/'evidence/h68/metadata-compilation.json').read_text())['fixtures']
assert {r['name'] for r in receipts}=={'ReaderFixtures','UnsupportedContract','YulKinds','ComposedReaders','ModalityControls'}
compiler=Path('/workspace/.setup/soljson/soljson-v0.8.34+commit.80d5c536.js')
assert sha(compiler)=='c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8'
rows=[]
for receipt in receipts:
 for path,key in [('source','sourceSha256'),('fixture','fixtureSha256'),('rawAst','rawAstSha256')]:assert sha(root/receipt[path])==receipt[key]
 assert receipt['compiler']['sha256']==sha(compiler)
 assert receipt['compiler']['version']=='0.8.34+commit.80d5c536.Emscripten.clang'
 fixture=json.loads((root/receipt['fixture']).read_text())
 previous=json.loads(subprocess.check_output(['git','show',pin+':'+receipt['baselineFixture']],cwd=root))
 assert strip(previous)==strip(fixture), 'nonmetadata change: '+receipt['name']
 raw=json.loads((root/receipt['rawAst']).read_text());index=collections.defaultdict(list)
 for n in walk(raw):
  if 'nodeType' in n:index[(n['nodeType'],n.get('src'))].append(n)
 identifiers=calls=0
 for n in walk(fixture['ast']):
  if 'nodeType' not in n:continue
  candidates=[r for r in index[(n['nodeType'],n.get('src'))] if 'id' not in n or r.get('id')==n['id']]
  assert candidates, 'missing raw identity'
  for r in candidates:
   if 'typeIdentifier' in r.get('typeDescriptions',{}):
    assert 'typeDescriptions' in n, 'normalized node lost required typeDescriptions'
    assert n['typeDescriptions']==r['typeDescriptions'], 'compiler metadata changed'
   if 'tryCall' in r:assert n['tryCall']==r['tryCall']
  identifiers+=int('typeIdentifier' in n.get('typeDescriptions',{}));calls+=int('tryCall' in n)
 rows.append({'name':receipt['name'],'compilerTypeIdentifiers':identifiers,'compilerTryCallFlags':calls,'allOtherBytesAsJsonValuesMatchRecordedPublication':True})
(bulk/'evidence/h68/metadata-preflight.json').write_text(json.dumps({'baseline':pin,'fixtures':rows,'boundary':'Compiler provenance and metadata/normalized-value controls; not semantic translation or source preservation proof.'},indent=2)+'\n')
print(json.dumps(rows))
