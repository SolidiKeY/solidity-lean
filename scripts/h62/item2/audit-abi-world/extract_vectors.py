#!/usr/bin/env python3
"""Extract only current, fully validated Lean Backend.encode output."""
import hashlib,json,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
from receipts import checked_receipt
root=Path(__file__).resolve().parents[4]
e=Path('/workspace/audit-abi-world-evidence')
source=root/'tests/h62/item2/audit-abi-world/H62AbiWorld/RuntimeVectors.lean'
d,_=checked_receipt(source,e)
p=e/'RuntimeVectors.json';r=json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
local={str(p.relative_to(root)):sha(p) for p in sorted(source.parent.glob('*.lean'))}
assert r['_vector_dependencies']['before']==local==r['_vector_dependencies']['after']
assert not subprocess.check_output(['git','diff','--name-only','c6f550e281a7e5affa9a99bc2cdaed556dec00e4','--','Solidity'],cwd=root).strip()
items=[x['message'][len('H62_VECTORS='):] for x in d['items'] if x['message'].startswith('H62_VECTORS=')]
assert len(items)==1
vectors=json.loads(items[0]);assert len(vectors)==10 and len({v['name'] for v in vectors})==10
assert all(v['compiled'] is True for v in vectors)
output=e/'runtime-vectors.json';output.write_text(json.dumps(vectors,indent=2)+'\n')
provenance=dict(root=str(root),source=str(source),source_sha256=sha(source),diagnostic=str(p),diagnostic_sha256=sha(p),resource=str(e/'RuntimeVectors-resource.json'),resource_sha256=sha(e/'RuntimeVectors-resource.json'),vectors_sha256=sha(output),local_sources=local,support=r['_audit']['support_before'],extractor_sha256=sha(Path(__file__)))
(e/'runtime-vectors-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
print('Extracted10 actual Backend.encode fixtures with current complete provenance')
