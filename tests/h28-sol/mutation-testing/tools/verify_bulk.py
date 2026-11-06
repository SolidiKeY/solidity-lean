"""Verify the committed H44 bulk manifest, all external/mirror files and archive."""
from pathlib import Path
import hashlib
import json
import subprocess
import tarfile
import time
import bulk_inputs
from archive_io import require

def digest(data):
    return hashlib.sha256(data).hexdigest()

def verify_snapshot_files(repo, manifest, entries):
    tracked = set(subprocess.check_output(['git', 'ls-files'], cwd=repo, text=True).splitlines())
    support = set(entries) & tracked
    require(support == set(manifest['retained_reviewable_support_files']), 'tracked support inventory changed')
    total = 0
    for rel, expected in entries.items():
        name = Path(rel)
        require(not name.is_absolute() and '..' not in name.parts and name.is_relative_to(bulk_inputs.PREFIX), 'unsafe snapshot path')
        external = Path(manifest['root']) / name
        require(external.is_file() and (not external.is_symlink()), 'invalid external snapshot file')
        data = external.read_bytes()
        require(len(data) == expected['bytes'] and digest(data) == expected['sha256'], 'external snapshot identity mismatch: ' + rel)
        mirror = repo / name
        if rel in support:
            mirror_data = bulk_inputs.read(repo, mirror)
            require(len(mirror_data) == expected['bytes'] and digest(mirror_data) == expected['sha256'], 'tracked mirror identity mismatch: ' + rel)
        else:
            require(mirror.is_file() and (not mirror.is_symlink()) and (mirror.read_bytes() == data), 'bulk mirror identity mismatch: ' + rel)
        total += expected['bytes']
    return total

def verify(repo):
    t = time.monotonic()
    pin = repo / bulk_inputs.PREFIX / 'bulk-data.json'
    m = json.loads(bulk_inputs.read(repo, pin))
    index_bytes = Path(m['index']).read_bytes()
    require(digest(index_bytes) == m['index_sha256'], 'bulk verification failed')
    entries = json.loads(index_bytes)['files']
    require(len(entries) == m['file_count'], 'bulk verification failed')
    total = verify_snapshot_files(repo, m, entries)
    require(total == m['uncompressed_bytes'], 'bulk verification failed')
    archive = Path(m['archive'])
    require(archive.stat().st_size == m['archive_bytes'] and digest(archive.read_bytes()) == m['archive_sha256'], 'bulk verification failed')
    seen = set()
    with tarfile.open(archive, 'r:gz') as tar:
        for member in tar:
            if member.isdir():
                continue
            require(member.isfile() and member.name not in seen and (not member.name.startswith('/')) and ('..' not in Path(member.name).parts), 'bulk verification failed')
            seen.add(member.name)
            if member.name.startswith('files/'):
                rel = member.name[len('files/'):]
                data = tar.extractfile(member).read()
                require(len(data) == entries[rel]['bytes'] and digest(data) == entries[rel]['sha256'], 'bulk verification failed')
            elif member.name == 'files.json':
                require(tar.extractfile(member).read() == index_bytes, 'bulk verification failed')
            else:
                require(member.name == 'SHA256SUMS', 'bulk verification failed')
        require(seen == {'files/' + p for p in entries} | {'files.json', 'SHA256SUMS'}, 'bulk verification failed')
    require(digest(Path(m['backup_bundle']).read_bytes()) == m['backup_bundle_sha256'], 'bulk verification failed')
    subprocess.run(['git', 'bundle', 'verify', m['backup_bundle']], cwd=repo, check=True, stdout=subprocess.DEVNULL)
    return {'status': 'pass', 'command': 'python3 -B tests/h28-sol/mutation-testing/tools/verify_bulk.py', 'files': len(entries), 'uncompressed_bytes': total, 'archive': str(archive), 'archive_bytes': m['archive_bytes'], 'sha256': m['archive_sha256'], 'backup_bundle_verified': True, 'seconds': time.monotonic() - t}
if __name__ == '__main__':
    repo = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True).strip())
    print(json.dumps(verify(repo), indent=2))
