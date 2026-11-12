#!/usr/bin/env python3
"""Recreate historical audit shards using their original producers and Git inputs."""
import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
HISTORICAL = 'dfdfa238b5bf63955048999fefd291d9d55dbd56'
INPUT = 'd4ad633a9624263a59b14fd2c520b9bc602f88f3'
LAUNCH = '005eec705a0f8b2a85ab73e3007a7aac69b43092'
PREFIX = 'docs/audits/direction-tools/'
OFFLINE_ENV = {**os.environ, 'GIT_NO_LAZY_FETCH': '1'}
SHARD_NAME = re.compile(r'(?:modules-|duplicates-)[^/]*\.json\Z')
SHARD = re.compile(r'docs/audits/direction-tools/(?:census/modules-[^/]*|reachability/duplicates-[^/]*)\.json\Z')

class VerificationError(Exception):
    pass

def git(*args, cwd=ROOT):
    try:
        return subprocess.check_output(['git', '-C', str(cwd), *args], env=OFFLINE_ENV)
    except subprocess.CalledProcessError as e:
        raise VerificationError('UNVERIFIABLE: Git command failed: ' + ' '.join(args)) from e

def tree(revision):
    entries = []
    for row in git('ls-tree', '-rlz', revision, '--', PREFIX).split(b'\0'):
        if not row:
            continue
        metadata, rawpath = row.split(b'\t', 1)
        mode, kind, oid, size = metadata.split()
        if kind != b'blob':
            raise VerificationError('non-blob tree entry: ' + os.fsdecode(rawpath))
        entries.append((os.fsdecode(rawpath), oid.decode(), int(size)))
    return entries

def unique(entries, label):
    paths = [e[0] for e in entries]
    if len(set(paths)) != len(paths):
        raise VerificationError('duplicate path in ' + label)
    return set(paths)

def validate_manifest(inventory, manifest, count=38, size=6452407):
    paths = unique(inventory, 'inventory')
    unique([(p,) for p in manifest], 'manifest')
    if len(inventory) != count or sum(e[2] for e in inventory) != size:
        raise VerificationError('UNVERIFIABLE: historical inventory count/size mismatch')
    if set(manifest) != paths:
        raise VerificationError('omitted or extra manifest entry: ' + repr(sorted(paths ^ set(manifest))))

def compare(expected, actual):
    unique(expected, 'expected')
    unique(actual, 'generated')
    want, got = dict(expected), dict(actual)
    missing, extra = want.keys() - got.keys(), got.keys() - want.keys()
    wrong = {p for p in extra if Path(p).name in {Path(q).name for q in want}}
    extra -= wrong
    if missing or extra or wrong:
        raise VerificationError(f'missing shards: {sorted(missing)}; wrong-path shards: {sorted(wrong)}; extra shards: {sorted(extra)}')
    changed = [p for p in want if want[p] != got[p]]
    if changed:
        raise VerificationError('changed shard bytes: ' + repr(sorted(changed)))

def verify_retained(expected, actual):
    unique(expected, 'retained expected')
    unique(actual, 'retained actual')
    current = dict(actual)
    missing = [p for p, _ in expected if p not in current]
    changed = [p for p, b in expected if p in current and current[p] != b]
    if missing or changed:
        raise VerificationError(f'missing retained entries: {missing}; changed retained entries: {changed}')

def reject_tracked(paths):
    if paths:
        raise VerificationError('reintroduced tracked shards: ' + repr(sorted(paths)))

def discover(root):
    return [(str(p.relative_to(root)), p.read_bytes()) for p in root.rglob('*.json')
            if p.is_file() and SHARD_NAME.fullmatch(p.name)]

def tracked_shards(root, historical_blobs=None):
    # Match shard-family names anywhere, and historical content even if renamed.
    historical_blobs = historical_blobs or {}
    found = set()
    checked = set()
    for row in git('ls-files', '-s', '-z', cwd=root).split(b'\0'):
        if not row:
            continue
        metadata, rawpath = row.split(b'\t', 1)
        _, oid, _ = metadata.split()
        path = os.fsdecode(rawpath)
        oid = oid.decode()
        if SHARD_NAME.fullmatch(Path(path).name):
            found.add(path)
        if oid in historical_blobs:
            if oid not in checked:
                if git('cat-file', 'blob', oid, cwd=root) != historical_blobs[oid]:
                    raise VerificationError('UNVERIFIABLE: indexed historical blob differs: ' + oid)
                checked.add(oid)
            found.add(path)
    return sorted(found)

def index_files(root, paths):
    rows = git('ls-files', '-s', '-z', '--', *paths, cwd=root).split(b'\0')
    result = []
    for row in rows:
        if not row:
            continue
        metadata, path = row.split(b'\t', 1)
        _, oid, stage = metadata.split()
        if stage != b'0':
            raise VerificationError('unmerged retained entry: ' + os.fsdecode(path))
        result.append((os.fsdecode(path), git('cat-file', 'blob', oid.decode(), cwd=root)))
    return result

def deletions(root, base):
    return [os.fsdecode(p) for p in git('diff', '--no-renames', '--name-only', '--diff-filter=D', '-z', base, cwd=root).split(b'\0') if p]

def blob(oid):
    return git('cat-file', 'blob', oid)

def run(*args, cwd):
    subprocess.run(args, cwd=cwd, check=True, env=OFFLINE_ENV)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true', required=True)
    ap.parse_args()
    historical = tree(HISTORICAL)
    unique(historical, 'historical tree')
    inventory = [e for e in historical if SHARD.fullmatch(e[0])]
    manifest = [e[0] for e in inventory]
    validate_manifest(inventory, manifest)
    expected = [(p, blob(oid)) for p, oid, _ in inventory]
    if any(len(b) != size for (_, b), (_, _, size) in zip(expected, inventory)):
        raise VerificationError('UNVERIFIABLE: Git blob size mismatch')
    launch = tree(LAUNCH)
    unique(launch, 'launch tree')
    launch_paths = {p for p, _, _ in launch}
    historical_retained = {p for p, _, _ in historical if not SHARD.fullmatch(p)}
    missing = sorted(p for p in historical_retained if p not in launch_paths or not (ROOT / p).is_file())
    if missing:
        raise VerificationError('missing historical retained paths: ' + repr(missing))
    retained = [(p, blob(oid)) for p, oid, _ in launch if not SHARD.fullmatch(p)]
    current = [(p, (ROOT / p).read_bytes()) for p, _ in retained if (ROOT / p).is_file()]
    verify_retained(retained, current)
    verify_retained(retained, index_files(ROOT, [p for p, _ in retained]))
    historical_blobs = {entry[1]: data for entry, (_, data) in zip(inventory, expected)}
    reject_tracked(tracked_shards(ROOT, historical_blobs))
    # Without a remote-tracking ref, conservatively compare against launch.
    merge_base = subprocess.run(['git', '-C', str(ROOT), 'merge-base', 'HEAD', 'origin/master'],
                                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=OFFLINE_ENV)
    task_base = os.fsdecode(merge_base.stdout).strip() if merge_base.returncode == 0 else LAUNCH
    removed = deletions(ROOT, task_base)
    if any(p not in manifest for p in removed):
        raise VerificationError('deletion outside permitted inventory: ' + repr(removed))
    sources = {p: oid for p, oid, _ in launch if p in (PREFIX + 'census/metrics.py', PREFIX + 'reachability/reach.py')}
    if len(sources) != 2:
        raise VerificationError('UNVERIFIABLE: producer source missing at launch')
    print(f'Historical revision: {HISTORICAL}; producer input: {INPUT}; launch revision: {LAUNCH}', flush=True)
    print(f'Producer source blobs at launch (verified byte-for-byte): {sources}', flush=True)
    print(f'Historical inventory: {len(inventory)} shards, {sum(e[2] for e in inventory)} bytes; retained launch files: {len(retained)}; historical retained paths: {len(historical_retained)}', flush=True)
    for path, _, size in inventory:
        print(f'  {path}: {size} bytes', flush=True)
    with tempfile.TemporaryDirectory(prefix='audit-regeneration-') as tmp:
        scratch = Path(tmp)
        # A linked Git directory gives the actual producer access to pinned blobs and history.
        gitdir = os.fsdecode(git('rev-parse', '--absolute-git-dir')).strip()
        (scratch / '.git').write_text('gitdir: ' + gitdir + '\n')
        # Do not copy local shard-family files into the generation tree.
        shutil.copytree(ROOT / PREFIX, scratch / PREFIX,
                        ignore=shutil.ignore_patterns('modules-*.json', 'duplicates-*.json'))
        census = scratch / PREFIX / 'census'
        reach = scratch / PREFIX / 'reachability'
        run(sys.executable, '-B', str(census / 'metrics.py'), '--rev', INPUT, '--out', str(census), cwd=scratch)
        # Check the regenerated chunks against the retained census and history.
        shutil.copy2(ROOT / PREFIX / 'census/census.json', census / 'census.json')
        run(sys.executable, '-B', str(census / 'check.py'), cwd=scratch)
        run(sys.executable, '-B', str(reach / 'reach.py'), cwd=scratch)
        compare(expected, discover(scratch))
        # Check mode must compare against the retained summaries, not its own writes.
        for name in ('reach.json', 'summary.json', 'unreachable.csv'):
            shutil.copy2(ROOT / PREFIX / 'reachability' / name, reach / name)
        run(sys.executable, '-B', str(reach / 'reach.py'), '--check', cwd=scratch)
    print('PASS full-byte regeneration, producer checks, retained files, and untracked shard inventory')

if __name__ == '__main__':
    try:
        main()
    except (VerificationError, subprocess.CalledProcessError, OSError) as exc:
        print('FAIL:', exc, file=sys.stderr)
        sys.exit(1)
