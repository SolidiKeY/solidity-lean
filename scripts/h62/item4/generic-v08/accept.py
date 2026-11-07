#!/usr/bin/env python3
"""Reproduce pinned lexical census; refuse any family change or lost case."""
import hashlib,json
from census import BASE,ROOT,inventory

def validate(expected, actual, manifest):
    raw=(json.dumps(expected,ensure_ascii=False,indent=2)+'\n').encode()
    checks=[
        (hashlib.sha256(raw).hexdigest()==manifest['inventory_sha256'],'frozen census fingerprint mismatch'),
        (expected['files']==manifest['files'],'frozen file hashes mismatch'),
        (len(expected['declarations'])==manifest['declaration_count'],'frozen declaration count mismatch'),
        (actual==expected,'working family differs from frozen source'),
        (len({(d['path'],d['ordinal']) for d in expected['declarations']})==len(expected['declarations']),'duplicate row identity')]
    for valid, reason in checks:
        if not valid: raise ValueError(reason)

def main():
    manifest=json.loads((ROOT/'tests/h62/item4/generic-v08/inventory-manifest.json').read_text())
    expected=inventory(ROOT,BASE)
    try: validate(expected,inventory(ROOT),manifest)
    except ValueError as error: raise SystemExit(f'FAIL: {error}')
    print(f"PASS census: {len(expected['files'])} files; {len(expected['declarations'])} declarations; sha256 {manifest['inventory_sha256']}")
    print('Boundary: lexical headers plus complete file integrity; not elaboration or semantic proof.')

if __name__=='__main__': main()
