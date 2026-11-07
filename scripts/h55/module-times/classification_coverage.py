#!/usr/bin/env python3
"""Guard regression: overlapping static references inflate standalone inventory coverage."""
import hashlib
import json
import re
from pathlib import Path
import sys


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def reconcile(old, delta, artifacts):
    if not isinstance(old, dict) or not isinstance(old.get('rows'), list):
        raise ValueError('invalid old census')
    changes = delta['delta']
    if changes['removed'] or changes['changed_bytes'] or changes['changed_mapping']:
        raise ValueError('delta requires explicit rebase of baseline')
    universe = {}
    for row in old['rows'] + changes['added']:
        if not isinstance(row, dict) or not isinstance(row.get('path'), str) or not isinstance(row.get('sha256'), str) or not re.fullmatch(r'[0-9a-f]{64}', row['sha256']) or row['path'] in universe:
            raise ValueError('invalid or duplicate baseline path')
        universe[row['path']] = row
    sources = {p: [] for p in universe}
    for label, doc in artifacts:
        if not isinstance(doc, dict) or not isinstance(doc.get('rows'), list):
            raise ValueError('invalid classification artifact')
        seen = set()
        for entry in doc['rows']:
            row = entry['candidate']
            path = row['path']
            if (path in seen or path not in universe or not isinstance(row.get('sha256'), str) or not re.fullmatch(r'[0-9a-f]{64}', row['sha256'])
                    or row.get('sha256') != universe[path]['sha256']):
                raise ValueError('duplicate, unknown or stale classification')
            seen.add(path)
            sources[path].append(label)
    return [{'candidate': universe[p], 'static_reference_artifacts': sorted(sources[p]),
             'status': 'referenced-not-runtime-accepted' if sources[p] else 'no-supplied-per-path-reference'}
            for p in sorted(universe)]


def main():
    if len(sys.argv) < 5:
        print('usage: classification_coverage.py OLD.json DELTA.json EARLIER.json CLASSIFICATION.json...', file=sys.stderr)
        return 2
    try:
        files = [Path(x) for x in sys.argv[1:]]
        if len({str(p.resolve()) for p in files}) != len(files):
            raise ValueError('duplicate input artifact')
        raws = [p.read_bytes() for p in files]
        docs = [json.loads(raw) for raw in raws]
        if digest(raws[0]) != docs[1]['old_snapshot_sha256']:
            raise ValueError('old snapshot digest mismatch')
        for artifact in docs[3:]:
            reference = artifact.get('census_sha256', artifact.get('input_sha256'))
            if reference not in (digest(raws[0]), digest(raws[1]), digest(raws[2])):
                raise ValueError('classification input digest is not supplied')
        rows = reconcile(docs[0], docs[1], [(str(p.resolve()), d) for p, d in zip(files[3:], docs[3:])])
        referenced = sum(bool(r['static_reference_artifacts']) for r in rows)
        print(json.dumps({'status': 'static-reference-index-not-execution-acceptance',
            'limitations': 'supplied subset of artifacts only; references retain unresolved inputs and outcomes; generated paths and current tree drift not covered',
            'baseline_head': docs[1]['head'],
            'inputs': [{'path': str(p.resolve()), 'sha256': digest(raw)} for p, raw in zip(files, raws)],
            'total': len(rows), 'referenced': referenced, 'unreferenced': len(rows)-referenced,
            'overlap': sum(len(r['static_reference_artifacts']) > 1 for r in rows), 'rows': rows}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'classification coverage unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
