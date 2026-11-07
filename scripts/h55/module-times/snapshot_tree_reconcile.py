#!/usr/bin/env python3
"""Guard regression: a candidate-set addition is silently reported as a new Git path."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]


def tree(rev):
    raw = subprocess.check_output(['git', 'ls-tree', '-rz', '--full-tree', rev, '--'], cwd=ROOT)
    result = {}
    for entry in raw.split(b'\0'):
        if not entry:
            continue
        header, path = entry.split(b'\t', 1)
        mode, kind, oid = header.decode('ascii').split()
        key = path.decode('utf-8')
        if key in result:
            raise ValueError('duplicate Git path')
        result[key] = {'mode': mode, 'kind': kind, 'oid': oid}
    return result


def reconcile(rows, old_tree, new_tree, load_blob):
    seen, result = set(), []
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get('path'), str) or row['path'] in seen:
            raise ValueError('invalid or duplicate candidate')
        path = row['path']
        seen.add(path)
        old, new = old_tree.get(path), new_tree.get(path)
        if not new or new['kind'] != 'blob' or new['mode'] not in ('100644', '100755'):
            raise ValueError('new tree entry is missing or not a regular file')
        digest = hashlib.sha256(load_blob(new['oid'])).hexdigest()
        if digest != row.get('sha256'):
            raise ValueError('new tree blob differs from observed row')
        result.append({'path': path, 'old_path_exists': old is not None,
                       'new_tree_entry': new, 'observed_sha256': digest,
                       'path_status': 'existing-path' if old else 'absent-at-old-tree'})
    return result


def main():
    if len(sys.argv) != 3:
        print('usage: snapshot_tree_reconcile.py OLD.json DELTA.json', file=sys.stderr)
        return 2
    try:
        old_raw, delta_raw = (Path(x).read_bytes() for x in sys.argv[1:])
        old, delta = json.loads(old_raw), json.loads(delta_raw)
        if hashlib.sha256(old_raw).hexdigest() != delta['old_snapshot_sha256']:
            raise ValueError('historical snapshot digest mismatch')
        old_head, new_head = old['head'], delta['head']
        subprocess.run(['git', 'merge-base', '--is-ancestor', old_head, new_head], cwd=ROOT, check=True)
        old_tree, new_tree = tree(old_head), tree(new_head)
        def blob(oid):
            return subprocess.check_output(['git', 'cat-file', 'blob', oid], cwd=ROOT)
        rows = reconcile(delta['delta']['added'], old_tree, new_tree, blob)
        print(json.dumps({'status': 'git-path-comparison-not-execution-acceptance',
            'old_head': old_head, 'new_head': new_head,
            'old_snapshot_sha256': hashlib.sha256(old_raw).hexdigest(),
            'delta_sha256': hashlib.sha256(delta_raw).hexdigest(),
            'limitations': 'path absence does not rule out renames or copied content; snapshot contexts and runtime inputs are not authenticated',
            'rows': rows}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        print(f'tree reconciliation unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
