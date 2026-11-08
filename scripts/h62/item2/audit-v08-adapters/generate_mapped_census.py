#!/usr/bin/env python3
"""Prepare bounded mapped-module diagnostics with the existing kernel collector.

Guards silent omission of non-theorem declarations from the lexical audit.
Generated source is not a Lean check, witness, or statement-fidelity acceptance.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
from census import frozen_blobs
from generate_calldata_census import render, TEMPLATE, OUTPUT_ROOT

MARKER = 'H62_MAPPED_CENSUS_JSON '


def prepare(repo, snapshot, paths, *, stream=False, result_shapes=False):
    if not paths or len(paths) > 4 or len(set(paths)) != len(paths):
        raise ValueError('Select one to four distinct mapped files')
    records = snapshot['modules']
    if len({r['file'] for r in records}) != len(records):
        raise ValueError('Duplicate snapshot module')
    mapped = {r['file']: r for r in records}
    frozen = frozen_blobs(repo)
    bindings = []
    modules = []
    for path in paths:
        if path not in mapped or path not in frozen:
            raise ValueError('Selection is not a frozen mapped module: ' + path)
        if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(/[A-Za-z_][A-Za-z0-9_]*)*\.lean', path) is None:
            raise ValueError('Unsupported Lean module spelling')
        data = subprocess.check_output(['git', 'cat-file', 'blob', frozen[path]], cwd=repo)
        digest = hashlib.sha256(data).hexdigest()
        if digest != mapped[path]['sha256']:
            raise ValueError('Snapshot/frozen blob mismatch: ' + path)
        current = repo / path
        if current.resolve() != current or current.read_bytes() != data:
            raise ValueError('Current import differs from frozen snapshot: ' + path)
        modules.append(path[:-5].replace('/', '.'))
        bindings.append(dict(file=path, blob=frozen[path], sha256=digest))
    template = (repo / TEMPLATE).read_text()
    return render(template, tuple(modules), MARKER, stream=stream, result_shapes=result_shapes), bindings, hashlib.sha256(template.encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--snapshot', type=Path, required=True)
    parser.add_argument('--file', action='append', required=True)
    parser.add_argument('--name', required=True)
    parser.add_argument('--expect-sha256')
    parser.add_argument('--result-shapes', action='store_true', help='Capture structural conclusion heads; no semantic acceptance')
    parser.add_argument('--stream', action='store_true', help='Skip global sort; retain selected rows and fields')
    args = parser.parse_args()
    repo = args.repo.resolve()
    if re.fullmatch(r'[A-Za-z][A-Za-z0-9_-]*', args.name) is None:
        raise ValueError('Output name must be a simple owned filename')
    root = repo / OUTPUT_ROOT
    if root.resolve() != root:
        raise ValueError('Output escapes the owned repository scope')
    raw = args.snapshot.read_bytes()
    source, bindings, template_sha = prepare(repo, json.loads(raw), args.file, stream=args.stream, result_shapes=args.result_shapes)
    digest = hashlib.sha256(source.encode()).hexdigest()
    if args.expect_sha256 is not None and args.expect_sha256 != digest:
        raise ValueError('Generated diagnostic hash differs from pinned packet')
    root.mkdir(parents=True, exist_ok=True)
    out = root / (args.name + '.lean')
    with out.open('x') as handle:
        handle.write(source)
    print(json.dumps(dict(status='GENERATED_NOT_LEAN_CHECKED', output=str(out),
                         sha256=digest, bindings=bindings,
                         template_sha256=template_sha, result_shapes=args.result_shapes, enumeration='stream' if args.stream else 'sorted',
                         snapshot_sha256=hashlib.sha256(raw).hexdigest()), sort_keys=True))


if __name__ == '__main__':
    main()
