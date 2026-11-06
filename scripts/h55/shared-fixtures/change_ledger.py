#!/usr/bin/env python3
"""Make a complete line-partition change ledger; never approve changed inputs."""
import argparse
import difflib
import hashlib
import json
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[3]
BASE = '4d3790eadb8a5212233bc7d5e345817476b2f590'
AREAS = ('Solidity/Lowering/V08', 'Solidity/Backend/StorageOps',
         'Solidity/Lowering/StorageOps', 'Solidity/Lowering/G19')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def partition(old, new):
    """Cover all original and candidate lines, including additions and deletions."""
    a, b = old.splitlines(keepends=True), new.splitlines(keepends=True)
    ops = difflib.SequenceMatcher(a=a, b=b, autojunk=False).get_opcodes()
    assert all(i1 <= i2 and j1 <= j2 for _, i1, i2, j1, j2 in ops)
    assert sum(i2-i1 for _, i1, i2, _, _ in ops) == len(a)
    assert sum(j2-j1 for _, _, _, j1, j2 in ops) == len(b)
    return [{'kind': tag, 'base_lines': [i1+1, i2], 'candidate_lines': [j1+1, j2],
             'base_sha256': sha(''.join(a[i1:i2]).encode()),
             'candidate_sha256': sha(''.join(b[j1:j2]).encode())}
            for tag, i1, i2, j1, j2 in ops]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', default=BASE, help='baseline Git commit')
    parser.add_argument('paths', nargs='*', help='explicit paths; default: all baseline Lean files in four areas')
    args = parser.parse_args()
    if args.paths:
        paths = args.paths
    else:
        listing = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', args.base, '--', *AREAS], cwd=ROOT, text=True)
        paths = [p for p in listing.splitlines() if p.endswith('.lean')]
    if not paths or len(set(paths)) != len(paths):
        parser.error('scope must be nonempty without duplicates')
    rows = []
    for name in sorted(paths):
        path = pathlib.PurePosixPath(name)
        if path.is_absolute() or '..' in path.parts or str(path) != name or path.suffix != '.lean':
            parser.error(f'invalid path: {name}')
        current = ROOT.joinpath(*path.parts)
        resolved = current.resolve(strict=True)
        if not resolved.is_relative_to(ROOT) or not resolved.is_file():
            parser.error(f'not a regular file inside checkout: {name}')
        old = subprocess.check_output(['git', 'show', f'{args.base}:{name}'], cwd=ROOT)
        new = resolved.read_bytes()
        segments = partition(old.decode('utf-8'), new.decode('utf-8'))
        rows.append({'path': name, 'base_sha256': sha(old), 'candidate_sha256': sha(new), 'segments': segments})
    changed = sum(r['base_sha256'] != r['candidate_sha256'] for r in rows)
    print(json.dumps({'base': args.base, 'files': rows, 'changed_files': changed,
                      'status': 'review_required' if changed else 'byte_identical',
                      'limitation': 'Line partition is not a Lean parser, statement-equivalence proof, case review or kernel gate.'}, sort_keys=True))
    return 1 if changed else 0


if __name__ == '__main__':
    raise SystemExit(main())
