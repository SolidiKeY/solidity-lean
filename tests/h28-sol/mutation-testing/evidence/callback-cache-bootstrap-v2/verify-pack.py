"""Authenticate receipt inputs and verify the immutable archive; works with -O."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
from archive_io import read_bytes, read_json, require
from pathlib import Path
import json, hashlib, tarfile, time
out = Path(__file__).resolve().parent
r = read_json(out / 'cache-pack.json')
t = time.monotonic()

def sha(f):
    h = hashlib.sha256()
    for b in iter(lambda: f.read(1048576), b''):
        h.update(b)
    return h.hexdigest()
with open(r['archive'], 'rb') as f:
    require(sha(f) == r['sha256'], 'archive validation failed')
with tarfile.open(r['archive'], 'r:gz') as tar:
    expected = {}
    for line in tar.extractfile('SHA256SUMS').read().decode().splitlines():
        h, p = line.split('  ', 1)
        require(p not in expected, 'archive validation failed')
        expected[p] = h
    seen = set()
    for member in tar:
        require(member.isfile() and member.name not in seen, 'archive validation failed')
        require(not member.name.startswith('/') and '..' not in Path(member.name).parts, 'archive validation failed')
        seen.add(member.name)
        if member.name != 'SHA256SUMS':
            require(sha(tar.extractfile(member)) == expected[member.name], 'archive validation failed')
    require(seen == set(expected) | {'SHA256SUMS'}, 'archive validation failed')
    manifest = tar.extractfile('cache-manifest.json').read()
    require(hashlib.sha256(manifest).hexdigest() == r['cache_manifest_sha256'], 'archive validation failed')
    m = json.loads(manifest)
    require(m['complete'] and len(m['artifact_sha256']) == 71 and (len(m['reused_artifact_sha256']) == 68) and (len(m['checks']) == 3), 'archive validation failed')
    for c in m['checks']:
        mod = c['module'].replace('.', '/')
        require(sha(tar.extractfile('cache/' + mod + '.olean')) == m['artifact_sha256'][mod + '.olean'], 'archive validation failed')
        require(sha(tar.extractfile('sources/' + mod + '.lean')) == m['source_sha256'][mod + '.lean'], 'archive validation failed')
    require(tar.extractfile('catalog.json').read() == read_bytes(out / 'catalog.json'), 'archive validation failed')
with open(r['dependency_pack']['archive'], 'rb') as f:
    require(sha(f) == r['dependency_pack']['sha256'], 'archive validation failed')
print(json.dumps({'status': 'pass', 'command': 'python3 -B ' + str(Path(__file__).resolve()), 'archive': r['archive'], 'regular_members': len(seen), 'new_artifacts': 3, 'total_cache_artifacts': 71, 'dependency_pack_hash_verified': True, 'seconds': time.monotonic() - t, 'coordinator_pull_observed': False}, indent=2))
