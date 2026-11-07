#!/usr/bin/env python3
"""Guard regression: rebasing a static index silently drops changed or removed references."""
import hashlib
import json
from pathlib import Path
import re
import sys

FIELDS = ('category', 'context', 'module', 'resolution', 'collision')


def valid_candidate(row):
    if not isinstance(row, dict) or not isinstance(row.get('path'), str) or not row['path']:
        raise ValueError('invalid candidate')
    sha = row.get('sha256')
    if (not isinstance(sha, str) or not re.fullmatch(r'[0-9a-f]{64}', sha)
            or any(f not in row for f in FIELDS) or not isinstance(row['collision'], bool)):
        raise ValueError('invalid candidate identity')


def valid_labels(labels):
    if (not isinstance(labels, list) or any(not isinstance(x, str) or not x or not Path(x).is_absolute()
            or str(Path(x)) != x or '..' in Path(x).parts for x in labels) or len(labels) != len(set(labels))):
        raise ValueError('invalid reference labels')


def rebase(index, drift):
    if not isinstance(index, dict) or not isinstance(index.get('rows'), list) or not isinstance(drift, dict) or not isinstance(drift.get('rows'), list):
        raise ValueError('invalid index or drift')
    tombstones = index.get('removed_from_candidate_set', [])
    if not isinstance(tombstones, list):
        raise ValueError('invalid prior tombstones')
    old = {}
    for item in index['rows']:
        candidate = item['candidate']; valid_candidate(candidate)
        path = candidate['path']
        if path in old:
            raise ValueError('duplicate baseline candidate')
        refs, history = item['current_static_references'], item['historical_references_require_review']
        valid_labels(refs); valid_labels(history)
        records = item.get('historical_reference_records', [])
        if not isinstance(records, list):
            raise ValueError('invalid historical records')
        for record in records:
            valid_candidate(record['candidate_at_reference'])
            valid_labels(record['artifact_paths'])
            if (record['candidate_at_reference']['path'] != path or record['status'] != 'historical-reference-needs-review'
                    or not set(record['artifact_paths']) <= set(history)):
                raise ValueError('invalid historical record provenance')
        if item['status'] != ('referenced-static-only' if refs else 'no-supplied-current-reference'):
            raise ValueError('inconsistent baseline status')
        old[path] = item
    tombstone_paths = set()
    for item in tombstones:
        candidate = item['candidate']; valid_candidate(candidate)
        path = candidate['path']
        if path in tombstone_paths or path in old:
            raise ValueError('duplicate prior tombstone')
        refs, history = item['current_static_references'], item['historical_references_require_review']
        valid_labels(refs); valid_labels(history)
        if item['status'] != ('referenced-static-only' if refs else 'no-supplied-current-reference'):
            raise ValueError('invalid prior tombstone status')
        records = item.get('historical_reference_records', [])
        if not isinstance(records, list):
            raise ValueError('invalid prior tombstone records')
        for record in records:
            valid_candidate(record['candidate_at_reference']); valid_labels(record['artifact_paths'])
            if (record['candidate_at_reference']['path'] != path or record['status'] != 'historical-reference-needs-review'
                    or not set(record['artifact_paths']) <= set(history)):
                raise ValueError('invalid prior tombstone history')
        tombstone_paths.add(path)
    out, seen = [], set()
    for item in drift['rows']:
        candidate = item['candidate']; valid_candidate(candidate)
        path, state = candidate['path'], item['state']
        if path in seen or path in tombstone_paths:
            raise ValueError('duplicate or reappearing tombstone candidate')
        seen.add(path)
        prior = old.get(path)
        refs, history = item['prior_reference_artifacts'], item['historical_references_require_review']
        valid_labels(refs); valid_labels(history)
        changed_bytes, changed_mapping = item['changed_bytes'], item['changed_mapping']
        if type(changed_bytes) is not bool or type(changed_mapping) is not bool:
            raise ValueError('invalid drift flags')
        records = [] if prior is None else list(prior.get('historical_reference_records', []))
        if prior is None:
            if state != 'new-candidate' or refs or history or changed_bytes or changed_mapping:
                raise ValueError('invalid new candidate')
            current = []
        else:
            previous = prior['candidate']
            byte_diff = previous['sha256'] != candidate['sha256']
            mapping_diff = any(previous[f] != candidate[f] for f in FIELDS)
            if changed_bytes != byte_diff or changed_mapping != mapping_diff or refs != prior['current_static_references']:
                raise ValueError('drift identity or references mismatch')
            expected_history = sorted(set(prior['historical_references_require_review'] + (refs if byte_diff or mapping_diff else [])))
            if sorted(history) != expected_history:
                raise ValueError('historical references lost or forged')
            expected_state = ('changed-candidate-review' if byte_diff or mapping_diff else
                              'referenced-static-only' if refs else 'no-supplied-per-path-reference')
            if state != expected_state:
                raise ValueError('drift state mismatch')
            current = [] if byte_diff or mapping_diff else list(refs)
            if (byte_diff or mapping_diff) and refs:
                records.append({'candidate_at_reference':previous, 'artifact_paths':list(refs), 'status':'historical-reference-needs-review'})
        out.append({'candidate':candidate, 'current_static_references':current,
                    'historical_references_require_review':history, 'historical_reference_records':records,
                    'status':'referenced-static-only' if current else 'no-supplied-current-reference'})
    removed = list(tombstones)
    for item in drift['removed_from_candidate_set']:
        path = item['candidate']['path']
        if path in seen or path not in old:
            raise ValueError('invalid removed candidate')
        prior = old[path]
        if (item['candidate'] != prior['candidate'] or item['static_reference_artifacts'] != prior['current_static_references']
                or item['historical_references_require_review'] != prior['historical_references_require_review']):
            raise ValueError('removed candidate provenance mismatch')
        seen.add(path)
        removed.append(prior)
    if not set(old) <= seen:
        raise ValueError('baseline candidate disappeared without removed record')
    return sorted(out,key=lambda x:x['candidate']['path']), sorted(removed,key=lambda x:x['candidate']['path'])


def main():
    if len(sys.argv) != 3:
        print('usage: rebase_reference_index.py INDEX.json EXTENDED_DRIFT.json', file=sys.stderr)
        return 2
    try:
        old_raw, drift_raw = (Path(x).read_bytes() for x in sys.argv[1:])
        old, drift = json.loads(old_raw), json.loads(drift_raw)
        if hashlib.sha256(old_raw).hexdigest() != drift['input_sha256']:
            raise ValueError('drift input digest mismatch')
        rows, removed = rebase(old, drift)
        n = sum(bool(r['current_static_references']) for r in rows)
        print(json.dumps({'status':'static-reference-index-not-execution-acceptance', 'snapshot_head':drift['head'],
            'input_index_sha256':hashlib.sha256(old_raw).hexdigest(), 'input_drift_sha256':hashlib.sha256(drift_raw).hexdigest(),
            'limitations':'supplied non-atomic static snapshot only; artifact labels do not authenticate bytes, mapping or execution',
            'total':len(rows), 'referenced':n, 'unreferenced':len(rows)-n,
            'historical_reference_review':sum(bool(r['historical_references_require_review']) for r in rows),
            'removed_from_candidate_set':removed, 'rows':rows}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'reference rebase unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
