#!/usr/bin/env python3
"""Reproduce pinned lexical census; refuse any family change or lost case."""
import hashlib,json
from census import BASE,ROOT,inventory
manifest=json.loads((ROOT/'tests/h62/item4/generic-v08/inventory-manifest.json').read_text())
expected=inventory(ROOT,BASE)
raw=(json.dumps(expected,ensure_ascii=False,indent=2)+'\n').encode()
assert hashlib.sha256(raw).hexdigest()==manifest['inventory_sha256'], 'frozen census fingerprint mismatch'
assert expected['files']==manifest['files'], 'frozen file hashes mismatch'
assert len(expected['declarations'])==manifest['declaration_count'], 'frozen declaration count mismatch'
assert inventory(ROOT)==expected, 'working family differs from frozen source'
assert len({(d['path'],d['ordinal']) for d in expected['declarations']})==len(expected['declarations'])
print(f"PASS census: {len(expected['files'])} files; {len(expected['declarations'])} declarations; sha256 {manifest['inventory_sha256']}")
print('Boundary: lexical headers plus complete file integrity; not elaboration or semantic proof.')
