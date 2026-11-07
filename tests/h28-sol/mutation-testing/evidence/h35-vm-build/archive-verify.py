"""Authenticate receipt inputs and verify the immutable archive; works with -O."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
from archive_io import read_bytes, read_json, require
from pathlib import Path
import hashlib, json, tarfile, time, resource
out = Path(__file__).resolve().parent
receipt = read_json(out / 'local-export.json')
catalog = read_json(out / 'catalog.json')
expected = {}

def sha(stream):
    h = hashlib.sha256()
    for block in iter(lambda: stream.read(1048576), b''):
        h.update(block)
    return h.hexdigest()
with tarfile.open(receipt['archive'], 'r:gz') as tar:
    for run in catalog['runs']:
        prefix = 'runs/' + run['run'] + '/'
        seal = tar.extractfile(prefix + 'SHA256SUMS').read().decode()
        for line in seal.splitlines():
            digest, name = line.split('  ', 1)
            expected[prefix + name] = digest
    for source, digest in catalog['owned_sources'].items():
        expected['source-snapshot/' + source] = digest
    dependencies = json.loads(tar.extractfile('dependency-cache/manifest.json').read())
    for name, digest in dependencies['artifact_sha256'].items():
        expected['dependency-cache/lib/lean/' + name] = digest
with open(receipt['archive'], 'rb') as stream:
    require(sha(stream) == receipt['sha256'], 'archive digest mismatch')
seen = set()
start = time.monotonic()
with tarfile.open(receipt['archive'], 'r:gz') as tar:
    for member in tar:
        if member.isdir():
            continue
        require(member.isfile() and member.name not in seen, member.name)
        seen.add(member.name)
        if member.name in expected:
            require(sha(tar.extractfile(member)) == expected[member.name], member.name)
require(set(expected) <= seen, 'archive validation failed')
print(json.dumps({'status': 'pass', 'command': 'python3 -B ' + str(Path(__file__).resolve()), 'archive': receipt['archive'], 'verified_members': len(expected), 'regular_members': len(seen), 'seconds': time.monotonic() - start, 'maxrss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss, 'cache_transport_receipt': None}, indent=2))
