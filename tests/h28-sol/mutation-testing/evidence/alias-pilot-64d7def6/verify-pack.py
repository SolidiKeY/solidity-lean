"""Authenticate receipt inputs and verify the immutable archive; works with -O."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
from archive_io import read_bytes, read_json, require
from pathlib import Path
import hashlib, json, tarfile, time
out = Path(__file__).resolve().parent
receipt = read_json(out / 'cache-pack.json')
catalog = read_json(out / 'catalog.json')

def sha(f):
    h = hashlib.sha256()
    for b in iter(lambda: f.read(1048576), b''):
        h.update(b)
    return h.hexdigest()
t = time.monotonic()
with open(receipt['archive'], 'rb') as f:
    require(sha(f) == receipt['sha256'], 'archive validation failed')
expected = {'sources/' + p: h for p, h in catalog['sources'].items()}
with tarfile.open(receipt['archive'], 'r:gz') as tar:
    for line in tar.extractfile('run/SHA256SUMS').read().decode().splitlines():
        h, n = line.split('  ', 1)
        expected['run/' + n] = h
    seen = set()
    metadata = {'run/SHA256SUMS', 'catalog.json', 'README.md'}
    for member in tar:
        if member.isdir():
            continue
        require(member.isfile() and member.name not in seen, 'archive validation failed')
        require(not member.name.startswith('/') and '..' not in Path(member.name).parts, 'archive validation failed')
        seen.add(member.name)
        if member.name in expected:
            require(sha(tar.extractfile(member)) == expected[member.name], member.name)
    require(seen == set(expected) | metadata, 'archive validation failed')
    require(tar.extractfile('catalog.json').read() == read_bytes(out / 'catalog.json'), 'archive validation failed')
with open(receipt['dependency_pack']['archive'], 'rb') as f:
    require(sha(f) == receipt['dependency_pack']['sha256'], 'archive validation failed')
print(json.dumps({'status': 'pass', 'command': 'python3 -B ' + str(Path(__file__).resolve()), 'archive': receipt['archive'], 'regular_members': len(seen), 'compiled_artifacts': len(catalog['compiled_artifacts']), 'dependency_pack_hash_verified': True, 'seconds': time.monotonic() - t, 'coordinator_pull_observed': False}, indent=2))
