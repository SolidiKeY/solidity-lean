#!/usr/bin/env python3
"""Guard regression: expanded index references silently cover later changed files."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import census
import mapping
import current_reference_drift

ROOT = Path(__file__).resolve().parents[3]


def reconcile(index, current):
    if not isinstance(index, dict) or not isinstance(index.get('rows'), list):
        raise ValueError('invalid extended index')
    old, history = [], {}
    for item in index['rows']:
        row = item['candidate']
        refs, historic = item['current_static_references'], item['historical_references_require_review']
        if not isinstance(refs, list) or not isinstance(historic, list):
            raise ValueError('invalid reference lists')
        if item['status'] != ('referenced-static-only' if refs else 'no-supplied-current-reference'):
            raise ValueError('inconsistent reference status')
        if row['path'] in history:
            raise ValueError('duplicate old candidate')
        history[row['path']] = historic
        old.append({'candidate': row, 'static_reference_artifacts': refs})
    # Validate historical labels even when the path was removed from the new set.
    def validate_labels(labels):
        if (any(not isinstance(x, str) or not x or not Path(x).is_absolute() or str(Path(x)) != x or '..' in Path(x).parts for x in labels)
                or len(labels) != len(set(labels))):
            raise ValueError('invalid historical references')
    for labels in history.values():
        validate_labels(labels)
    rows, removed = current_reference_drift.reconcile(old, current)
    for row in rows:
        prior_history = history.get(row['candidate']['path'], [])
        stale = row['prior_reference_artifacts'] if row['state'] == 'changed-candidate-review' else []
        row['historical_references_require_review'] = sorted(set(prior_history + stale))
    for row in removed:
        row['historical_references_require_review'] = history[row['candidate']['path']]
    return rows, removed


def main():
    if len(sys.argv) != 2:
        print('usage: current_extended_drift.py EXTENDED_INDEX.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        old = json.loads(raw)
        before = subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip()
        subprocess.run(['git','diff','--quiet','HEAD','--','*.lean'], cwd=ROOT, check=True)
        mapped = mapping.derive(census.census(ROOT))
        subprocess.run(['git','diff','--quiet','HEAD','--','*.lean'], cwd=ROOT, check=True)
        after = subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip()
        if before != after:
            raise ValueError('HEAD changed while sampling')
        rows, removed = reconcile(old, [r for r in mapped if r['resolution'] == 'file-check-review'])
        untracked = subprocess.check_output(['git','ls-files','--others','--exclude-standard','-z','--','*.lean'], cwd=ROOT)
        counts = {state:sum(r['state']==state for r in rows) for state in ('new-candidate','changed-candidate-review','referenced-static-only','no-supplied-per-path-reference')}
        print(json.dumps({'status':'tracked-static-observation-not-runtime-acceptance','head':before,
            'input_sha256':hashlib.sha256(raw).hexdigest(),
            'census_sha256':hashlib.sha256((ROOT/'scripts/h55/module-times/census.py').read_bytes()).hexdigest(),
            'mapper_sha256':hashlib.sha256((ROOT/'scripts/h55/module-times/mapping.py').read_bytes()).hexdigest(),
            'limitations':'non-atomic index/worktree scan; index flags, ignored/generated paths, runtime and candidate resolution remain unverified',
            'tracked_total':len(mapped),'counts':counts,'removed_from_candidate_set':removed,
            'untracked_nonignored_lean':[p.decode('utf-8') for p in untracked.split(b'\0') if p], 'rows':rows}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        print(f'extended drift unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
