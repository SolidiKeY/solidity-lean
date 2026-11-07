#!/usr/bin/env python3
"""Guard regression: old references silently cover changed standalone source bytes."""
import hashlib
import json
from pathlib import Path
import re
import sys


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


MAPPING_FIELDS = ('category', 'context', 'module', 'resolution', 'collision')


def update(drift, artifacts):
    if not isinstance(drift, dict) or not isinstance(drift.get('rows'), list):
        raise ValueError('invalid drift snapshot')
    rows = {}
    for entry in drift['rows']:
        candidate = entry['candidate']
        path, sha, state = candidate['path'], candidate['sha256'], entry['state']
        refs = entry['prior_reference_artifacts']
        if (not isinstance(path, str) or not path or path in rows or not isinstance(sha, str)
                or not re.fullmatch(r'[0-9a-f]{64}', sha) or any(f not in candidate for f in MAPPING_FIELDS)
                or not isinstance(candidate['collision'], bool) or not isinstance(refs, list)
                or any(not isinstance(x, str) or not x for x in refs) or len(set(refs)) != len(refs)):
            raise ValueError('invalid drift row')
        if state not in ('new-candidate','changed-candidate-review','referenced-static-only','no-supplied-per-path-reference'):
            raise ValueError('invalid drift state')
        if state in ('new-candidate','no-supplied-per-path-reference') and refs:
            raise ValueError('unexpected prior reference')
        if state == 'referenced-static-only' and not refs:
            raise ValueError('missing prior reference')
        rows[path] = {'candidate': candidate, 'prior_state': state,
                      'current_static_references': list(refs) if state == 'referenced-static-only' else [],
                      'historical_references_require_review': list(refs) if state == 'changed-candidate-review' else []}
    for label, doc in artifacts:
        if not isinstance(doc, dict) or not isinstance(doc.get('rows'), list):
            raise ValueError('invalid classification artifact')
        seen = set()
        for entry in doc['rows']:
            row = entry['candidate']
            path = row['path']
            if (path in seen or path not in rows or row.get('sha256') != rows[path]['candidate']['sha256']
                    or any(f not in row or row[f] != rows[path]['candidate'][f] for f in MAPPING_FIELDS)):
                raise ValueError('duplicate, unknown or stale classification')
            seen.add(path)
            if label in rows[path]['current_static_references']:
                raise ValueError('duplicate classification label')
            rows[path]['current_static_references'].append(label)
    return [{'candidate': r['candidate'], 'prior_state': r['prior_state'],
             'current_static_references': sorted(r['current_static_references']),
             'historical_references_require_review': sorted(r['historical_references_require_review']),
             'status': 'referenced-static-only' if r['current_static_references'] else 'no-supplied-current-reference'}
            for _, r in sorted(rows.items())]


def main():
    if len(sys.argv) < 5:
        print('usage: reference_index_update.py DRIFT.json COVERAGE.json DELTA.json CLASSIFICATION.json...', file=sys.stderr)
        return 2
    try:
        files = [Path(x) for x in sys.argv[1:]]
        if len({str(p.resolve()) for p in files}) != len(files):
            raise ValueError('duplicate input artifact')
        raws = [p.read_bytes() for p in files]
        docs = [json.loads(raw) for raw in raws]
        if docs[0]['input_sha256'] != digest(raws[1]):
            raise ValueError('drift coverage digest mismatch')
        if digest(raws[2]) not in {item['sha256'] for item in docs[1]['inputs']}:
            raise ValueError('coverage delta digest mismatch')
        for artifact in docs[3:]:
            if artifact.get('input_sha256') not in {digest(raws[0]), digest(raws[1]), digest(raws[2])}:
                raise ValueError('classification input digest is not supplied')
        rows = update(docs[0], [(str(p.resolve()), d) for p, d in zip(files[3:], docs[3:])])
        referenced = sum(bool(r['current_static_references']) for r in rows)
        print(json.dumps({'status':'static-reference-index-not-execution-acceptance', 'snapshot_head':docs[0]['head'],
            'limitations':'supplied snapshot and artifacts only; references do not resolve execution; ignored/generated inputs, later changes and runtime are not covered',
            'inputs':[{'path':str(p.resolve()), 'sha256':digest(raw)} for p, raw in zip(files, raws)],
            'total':len(rows), 'referenced':referenced, 'unreferenced':len(rows)-referenced,
            'historical_reference_review':sum(bool(r['historical_references_require_review']) for r in rows),
            'overlap':sum(len(r['current_static_references'])>1 for r in rows), 'rows':rows}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'reference index update unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
