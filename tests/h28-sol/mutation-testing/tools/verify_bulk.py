#!/usr/bin/env python3
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

def verify_h44_member_manifest(repo, pin):
    relative = Path(pin["member_manifest"])
    require(not relative.is_absolute() and ".." not in relative.parts and relative.is_relative_to(bulk_inputs.PREFIX), "unsafe member manifest path")
    manifest = json.loads(bulk_inputs.read(repo, repo / relative))
    require(manifest["schema"] == 1 and manifest["authorization"] == "H44", "unsupported member manifest")
    require((manifest["archive"], manifest["archive_bytes"], manifest["archive_sha256"]) == (pin["archive"], pin["bytes"], pin["sha256"]), "member manifest archive mismatch")
    expected = manifest["members"]; seen = set()
    if "members" in pin:
        require(len(expected) == pin["members"], "archive member count mismatch")
    with tarfile.open(pin["archive"], "r:gz") as archive:
        for member in archive:
            require(member.isfile() and member.name not in seen and not member.name.startswith("/") and ".." not in Path(member.name).parts, "unsafe archive member")
            require(member.name in expected, "archive membership mismatch")
            seen.add(member.name); data = archive.extractfile(member).read()
            require(len(data) == expected[member.name]["bytes"] and digest(data) == expected[member.name]["sha256"], "archive member identity mismatch")
    require(seen == set(expected), "archive membership mismatch")
    return len(seen)


def verify_validation_archives(manifest, repo=None):
    """Hash validation/review archives and authenticate every declared member map."""
    verified = []
    def walk(value, path=()):
        if not isinstance(value, dict):
            return
        if "member_manifest" in value:
            require("archive" in value, "member manifest pin missing archive")
        if "archive" in value and ("member_manifest" in value or any("validation" in key or "review" in key for key in path)):
            archive = Path(value["archive"])
            require(archive.is_absolute() and archive.is_file() and not archive.is_symlink(), "invalid validation archive")
            require(archive.stat().st_size == value["bytes"] and digest(archive.read_bytes()) == value["sha256"], "validation archive identity mismatch")
            if "member_manifest" in value:
                require(repo is not None, "member verification requires repository")
                verify_h44_member_manifest(repo, value)
            verified.append(".".join(path))
        for key, child in value.items():
            walk(child, path + (key,))
    walk(manifest)
    return verified


def verify_frozen_manifest_inputs(repo, manifest, entries):
    """Explicit VM-only H44 declarations must match index and actual bytes."""
    verified = []
    for relative, pins in manifest.get("frozen_manifest_inputs", {}).items():
        config = json.loads(bulk_inputs.read(repo, repo / relative))
        require(config["input_storage"] == {"authorization": "H44", "availability": "VM-only", "bulk_manifest": str(bulk_inputs.PREFIX / "bulk-data.json"), "inputs": pins}, "off-Git input declaration mismatch")
        require({pin["role"] for pin in pins} == {"inventory", "cache_manifest"} and len(pins) == 2, "off-Git role inventory mismatch")
        for pin in pins:
            name = pin["path"]
            require(config[pin["role"]] == name and config[pin["role"] + "_sha256"] == pin["sha256"], "frozen manifest input pin mismatch")
            require(entries[name] == {"bytes": pin["bytes"], "sha256": pin["sha256"]}, "off-Git index pin mismatch")
            data = bulk_inputs.read(repo, repo / name)
            require(len(data) == pin["bytes"] and digest(data) == pin["sha256"], "off-Git input identity mismatch")
            verified.append(name)
    return verified


def verify(repo):
    t = time.monotonic()
    pin = repo / bulk_inputs.PREFIX / 'bulk-data.json'
    m = json.loads(bulk_inputs.read(repo, pin))
    index_bytes = Path(m['index']).read_bytes()
    require(digest(index_bytes) == m['index_sha256'], 'bulk verification failed')
    entries = json.loads(index_bytes)['files']
    require(len(entries) == m['file_count'], 'bulk verification failed')
    external_inputs = verify_frozen_manifest_inputs(repo, m, entries)
    validation_archives = verify_validation_archives(m, repo)
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
    return {'status': 'pass', 'validation_archives': validation_archives, 'explicit_off_git_inputs': external_inputs, 'command': 'python3 -B tests/h28-sol/mutation-testing/tools/verify_bulk.py', 'files': len(entries), 'uncompressed_bytes': total, 'archive': str(archive), 'archive_bytes': m['archive_bytes'], 'sha256': m['archive_sha256'], 'backup_bundle_verified': True, 'seconds': time.monotonic() - t}
def verify_local(repo):
    """What a checkout without the Codex VM's `/workspace` data can check.

    The H44 index, archive, bundle and validation archives live only on the
    Codex VM; their digests are never re-derived or faked here.  This checks
    the committed side: the manifest is the committed one, every explicit
    off-Git input pin against the bytes present in the checkout (fresh sha256
    over repository-relative paths), and every retained support file is
    tracked and unchanged.  The result is `local-only`, never `pass`.
    """
    pin = bulk_inputs.PREFIX / 'bulk-data.json'
    head = subprocess.check_output(['git', 'show', 'HEAD:' + str(pin)], cwd=repo)
    require((repo / pin).read_bytes() == head, 'bulk manifest differs from committed input')
    m = json.loads(head)
    tracked = set(subprocess.check_output(['git', 'ls-files'], cwd=repo, text=True).splitlines())
    inputs, absent = {}, []
    for relative, pins in m.get('frozen_manifest_inputs', {}).items():
        require(relative in tracked, 'frozen manifest not tracked: ' + relative)
        config = json.loads((repo / relative).read_bytes())
        for p in pins:
            name = Path(p['path'])
            require(not name.is_absolute() and '..' not in name.parts and name.is_relative_to(bulk_inputs.PREFIX), 'unsafe input path')
            require(config[p['role']] == p['path'] and config[p['role'] + '_sha256'] == p['sha256'], 'frozen manifest input pin mismatch')
            f = repo / name
            if not f.is_file():
                absent.append(p['path'])
                continue
            require(not f.is_symlink(), 'input must not be a symlink')
            data = f.read_bytes()
            require(len(data) == p['bytes'] and digest(data) == p['sha256'], 'local input identity mismatch: ' + p['path'])
            inputs[p['path']] = {'sha256': digest(data), 'bytes': len(data), 'tracked': p['path'] in tracked}
    for rel in m['retained_reviewable_support_files']:
        require(rel in tracked, 'support file not tracked: ' + rel)
        require((repo / rel).read_bytes() == subprocess.check_output(['git', 'show', 'HEAD:' + rel], cwd=repo), 'support file differs from HEAD: ' + rel)
    external = [m['index'], m['archive'], m['backup_bundle']]
    return {'status': 'local-only', 'verified_inputs': inputs,
            'absent_codex_vm_only': sorted(set(absent)),
            'support_files_tracked': len(m['retained_reviewable_support_files']),
            'unverifiable_here': [x for x in external if not Path(x).exists()],
            'command': 'python3 -B tests/h28-sol/mutation-testing/tools/verify_bulk.py --local'}


if __name__ == '__main__':
    import sys
    repo = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True).strip())
    m = json.loads((repo / bulk_inputs.PREFIX / 'bulk-data.json').read_bytes())
    if '--local' in sys.argv or not Path(m['index']).exists():
        # The external data is absent (any VM but the Codex one): say so and
        # check the committed side, instead of a traceback.
        print(json.dumps(verify_local(repo), indent=2))
        sys.exit(3)  # local-only is never a pass
    else:
        print(json.dumps(verify(repo), indent=2))
