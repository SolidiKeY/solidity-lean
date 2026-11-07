#!/usr/bin/env python3
"""Recover the pinned source ledger from Git; never a Lean or old-evidence claim.

Guarded regression: current master sources or reconstructed output must not be
silently substituted for the frozen source census or original worker evidence.
Bulk snapshots and ledgers stay outside Git; existing destinations are refused.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

BASE = 'c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
FINAL = '42e78a67e07fd786cb744036e7a4e53b0324ad65'
MANIFEST = 'tests/h62/item2/audit-v07-lowering/retirement/scope-manifest.json'
MANIFEST_SHA = '1d4682cc0a4055d1513a868e3162b12edff1424847d180aa1dc1077d10c8a644'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def reproduce(repo, output):
    repo, output = repo.resolve(), output.resolve()
    if output == repo or repo in output.parents:
        raise ValueError('bulk destination must be outside the checkout')
    if output.exists():
        raise FileExistsError('refusing existing destination')
    def blob(rev, path):
        return subprocess.check_output(['git', '-C', str(repo), 'show', rev+':'+path])
    manifest_bytes = blob(FINAL, MANIFEST)
    if sha(manifest_bytes) != MANIFEST_SHA:
        raise ValueError('retirement scope authentication failed')
    manifest = json.loads(manifest_bytes)
    if manifest['original_base'] != BASE:
        raise ValueError('wrong frozen base')
    pinned = [manifest['module_map'], *manifest['mapped_modules']]
    payload = {}
    for row in pinned:
        raw = blob(BASE, row['path'])
        if sha(raw) != row['sha256']:
            raise ValueError('frozen source mismatch: '+row['path'])
        payload[row['path']] = raw
    for path in manifest['supplemental_read_only_sources']:
        payload.setdefault(path, blob(BASE, path))
    for path in payload:
        if Path(path).is_absolute() or '..' in Path(path).parts:
            raise ValueError('nonrelative source path')
    output.mkdir(parents=True)
    snapshot = output/'snapshot'
    for path, raw in payload.items():
        destination = snapshot/path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(raw)
    (output/'scope-manifest.json').write_bytes(manifest_bytes)
    tools = Path(__file__).resolve().parent
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    outcomes = []
    def run(name, args):
        command = [sys.executable, str(tools/name), *map(str, args)]
        started = time.monotonic()
        result = subprocess.run(command, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log_name = f'{len(outcomes)+1:02d}-{name}.log'
        (output/log_name).write_bytes(result.stdout)
        outcomes.append(dict(command=command, log=log_name, exit=result.returncode,
                             seconds=round(time.monotonic()-started, 3)))
        if result.returncode:
            raise RuntimeError('reproduction failed; retained log: '+name)
    source = output/'source-inventory.json'
    dependencies = output/'dependency-inventory.json'
    semantic = output/'semantic-inventory.json'
    run('source_inventory.py', ['--repo', snapshot, '--output', source])
    run('dependency_inventory.py', ['--repo', snapshot, '--output', dependencies])
    run('verify-source-inventory.py', ['--repo', snapshot, '--inventory', source,
                                    '--dependencies', dependencies])
    run('semantic_inventory.py', ['--repo', snapshot, '--inventory', source, '--output', semantic])
    run('check-semantic-inventory.py', ['--repo', snapshot, '--source', source, '--semantic', semantic])
    for generator, artifact in [('source_inventory.py', source),
                                ('dependency_inventory.py', dependencies),
                                ('semantic_inventory.py', semantic)]:
        repeat = output/(artifact.stem+'-repeat.json')
        args = ['--repo', snapshot, '--output', repeat]
        if generator == 'semantic_inventory.py':
            args += ['--inventory', source]
        run(generator, args)
        if artifact.read_bytes() != repeat.read_bytes():
            raise ValueError('nondeterministic output: '+generator)
    record = dict(schema_version=1, base=BASE, retirement_head=FINAL,
                  scope_manifest_sha256=MANIFEST_SHA,
                  boundary='Reconstructed source-only evidence, not the original evidence packet or Lean validation.',
                  source_files=len(payload), commands=outcomes,
                  tool_hashes={p.name: sha(p.read_bytes()) for p in tools.glob('*.py')},
                  artifacts={p.name: sha(p.read_bytes()) for p in [source, dependencies, semantic]})
    (output/'reproduction.json').write_text(json.dumps(record, indent=2)+'\n')
    files = sorted(p for p in output.rglob('*') if p.is_file())
    (output/'SHA256SUMS').write_text(''.join(sha(p.read_bytes())+'  '+str(p.relative_to(output))+'\n' for p in files))
    return record


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(reproduce(args.repo, args.output), indent=2))
