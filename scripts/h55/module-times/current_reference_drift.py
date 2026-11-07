#!/usr/bin/env python3
"""Guard regression: old per-path references silently cover changed or new Lean files."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import census
import mapping

ROOT = Path(__file__).resolve().parents[3]


def reconcile(old_rows, current_rows):
    def keyed(rows, old):
        out = {}
        for item in rows:
            row = item['candidate'] if old else item
            path, sha = row['path'], row['sha256']
            if not isinstance(path, str) or not isinstance(sha, str) or not re.fullmatch(r'[0-9a-f]{64}', sha) or path in out:
                raise ValueError('invalid or duplicate candidate')
            if old:
                refs = item['static_reference_artifacts']
                if (not isinstance(refs, list) or any(not isinstance(x, str) or not x or not Path(x).is_absolute() or str(Path(x)) != x or '..' in Path(x).parts for x in refs)
                        or len(refs) != len(set(refs))):
                    raise ValueError('invalid references')
            out[path] = item
        return out
    a, b = keyed(old_rows, True), keyed(current_rows, False)
    fields = ('category', 'context', 'module', 'resolution', 'collision')
    rows = []
    for path in sorted(b):
        current, prior = b[path], a.get(path)
        references = [] if prior is None else prior['static_reference_artifacts']
        if not isinstance(references, list) or any(not isinstance(x, str) for x in references):
            raise ValueError('invalid references')
        changed_bytes = prior is not None and prior['candidate']['sha256'] != current['sha256']
        changed_mapping = prior is not None and any(prior['candidate'].get(f) != current.get(f) for f in fields)
        state = ('new-candidate' if prior is None else 'changed-candidate-review' if changed_bytes or changed_mapping else
                 'referenced-static-only' if references else 'no-supplied-per-path-reference')
        rows.append({'candidate': current, 'state': state, 'prior_reference_artifacts': references,
                     'changed_bytes': changed_bytes, 'changed_mapping': changed_mapping})
    return rows, [a[p] for p in sorted(a.keys() - b.keys())]


def main():
    if len(sys.argv) != 2:
        print('usage: current_reference_drift.py COVERAGE.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        old = json.loads(raw)
        before = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
        subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', '*.lean'], cwd=ROOT, check=True)
        mapped = mapping.derive(census.census(ROOT))
        subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', '*.lean'], cwd=ROOT, check=True)
        after = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
        if before != after:
            raise ValueError('HEAD changed while sampling')
        rows, removed = reconcile(old['rows'], [r for r in mapped if r['resolution'] == 'file-check-review'])
        untracked = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard', '-z', '--', '*.lean'], cwd=ROOT)
        counts = {state: sum(r['state'] == state for r in rows) for state in ('new-candidate', 'changed-candidate-review', 'referenced-static-only', 'no-supplied-per-path-reference')}
        print(json.dumps({'status': 'tracked-static-observation-not-runtime-acceptance', 'head': before,
            'input_sha256': hashlib.sha256(raw).hexdigest(), 'mapper_sha256': hashlib.sha256((ROOT/'scripts/h55/module-times/mapping.py').read_bytes()).hexdigest(),
            'census_sha256': hashlib.sha256((ROOT/'scripts/h55/module-times/census.py').read_bytes()).hexdigest(),
            'limitations': 'index/worktree scan is non-atomic and index flags may hide edits; candidate-set changes may be reclassification; ignored/generated inputs and runtime are not covered',
            'tracked_total': len(mapped), 'counts': counts, 'removed_from_candidate_set': removed,
            'untracked_nonignored_lean': [p.decode('utf-8') for p in untracked.split(b'\0') if p], 'rows': rows}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        print(f'current reference drift unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
