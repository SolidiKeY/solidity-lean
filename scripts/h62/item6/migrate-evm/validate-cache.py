"""Fail-closed provenance preflight for old/new private inventory caches."""
import hashlib,json,sys
from pathlib import Path
root,cache,version=Path(sys.argv[1]),Path(sys.argv[2]),sys.argv[3]
census_path=Path(sys.argv[4]) if len(sys.argv)>4 else Path('/workspace/migrate-evm-artifacts/evidence/base-census.json')
census=json.loads(census_path.read_text())
s=json.loads((cache/'summary.json').read_text())
assert s['stop'] is None and s['checked']==s['required']==len(census['order']), 'incomplete cache'
assert f'version {version},' in s['versions']['lean'], 'wrong compiler version'
assert [r['module'] for r in s['results']]==census['order'], 'wrong module closure'
assert all(r['exit']==0 and r['stop'] is None for r in s['results']), 'failed cache entry'
for mod,record in census['modules'].items():
    assert hashlib.sha256((root/record['path']).read_bytes()).hexdigest()==record['sha256'], 'source drift: '+mod
    assert (cache/'lib'/(mod.replace('.','/')+'.olean')).is_file(), 'missing olean: '+mod
print('Completed cache/version/frozen-source preflight PASS',file=sys.stderr)
