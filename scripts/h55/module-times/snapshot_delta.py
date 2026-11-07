#!/usr/bin/env python3
"""Guard regression: old standalone census silently omits newly merged paths."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import census
import mapping

ROOT = Path(__file__).resolve().parents[3]


def delta(old, current):
    if not isinstance(old, list) or not isinstance(current, list):
        raise ValueError('rows must be lists')
    def keyed(rows):
        result = {}
        for row in rows:
            if not isinstance(row, dict) or not isinstance(row.get('path'), str) or row['path'] in result:
                raise ValueError('invalid or duplicate path')
            result[row['path']] = row
        return result
    a, b = keyed(old), keyed(current)
    common = a.keys() & b.keys()
    fields = ('category', 'context', 'module', 'resolution', 'collision')
    return {'added': [b[p] for p in sorted(b.keys() - a.keys())],
            'removed': [a[p] for p in sorted(a.keys() - b.keys())],
            'changed_bytes': [p for p in sorted(common) if a[p].get('sha256') != b[p].get('sha256')],
            'changed_mapping': [p for p in sorted(common) if any(a[p].get(f) != b[p].get(f) for f in fields)]}


def main():
    if len(sys.argv) != 2:
        print('usage: snapshot_delta.py OLD_STANDALONE.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        old = json.loads(raw)
        if not isinstance(old, dict) or not isinstance(old.get('rows'), list):
            raise ValueError('invalid historical snapshot')
        before = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
        subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', '*.lean'], cwd=ROOT, check=True)
        rows = mapping.derive(census.census(ROOT))
        subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', '*.lean'], cwd=ROOT, check=True)
        after = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
        if before != after:
            raise ValueError('HEAD changed while sampling')
        standalone = [r for r in rows if r['resolution'] == 'file-check-review']
        generated = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard', '-z', '--', '*.lean'], cwd=ROOT)
        print(json.dumps({'status': 'tracked-static-observation-not-acceptance',
            'limitations': 'standalone-set changes may be reclassification; index/worktree observation is non-atomic and index flags can hide edits; ignored/generated inputs and Lake resolution are not covered',
            'head': before, 'old_snapshot_sha256': hashlib.sha256(raw).hexdigest(),
            'mapper_sha256': hashlib.sha256((ROOT/'scripts/h55/module-times/mapping.py').read_bytes()).hexdigest(),
            'census_sha256': hashlib.sha256((ROOT/'scripts/h55/module-times/census.py').read_bytes()).hexdigest(),
            'tracked_total': len(rows), 'standalone_total': len(standalone),
            'untracked_nonignored_lean': [p.decode('utf-8') for p in generated.split(b'\0') if p],
            'delta': delta(old['rows'], standalone)}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, subprocess.CalledProcessError) as exc:
        print(f'snapshot comparison unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
