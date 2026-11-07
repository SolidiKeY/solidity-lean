#!/usr/bin/env python3
"""Guard regression: stale or overlapping fixture references inflate inventory coverage."""
import hashlib
import json
from pathlib import Path
import re
import sys

FIELDS = ('category', 'context', 'module', 'resolution', 'collision')


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def extend(index, artifacts):
    if not isinstance(index, dict) or not isinstance(index.get('rows'), list):
        raise ValueError('invalid reference index')
    tombstones = index.get('removed_from_candidate_set', [])
    if not isinstance(tombstones, list) or tombstones:
        raise ValueError('historical-record or tombstone schema is unsupported')
    for item in index['rows']:
        records = item.get('historical_reference_records', [])
        if not isinstance(records, list) or records:
            raise ValueError('historical-record or tombstone schema is unsupported')
    rows = {}
    for entry in index['rows']:
        candidate = entry['candidate']
        path, sha = candidate['path'], candidate['sha256']
        refs, historical = entry['current_static_references'], entry['historical_references_require_review']
        if (not isinstance(path, str) or not path or path in rows or not isinstance(sha, str)
                or not re.fullmatch(r'[0-9a-f]{64}', sha) or any(f not in candidate for f in FIELDS)
                or not isinstance(candidate['collision'], bool) or not isinstance(refs, list) or not isinstance(historical, list)
                or any(not isinstance(x, str) or not x for x in refs + historical)
                or len(refs) != len(set(refs)) or len(historical) != len(set(historical))):
            raise ValueError('invalid baseline row')
        if entry['status'] != ('referenced-static-only' if refs else 'no-supplied-current-reference'):
            raise ValueError('inconsistent baseline status')
        rows[path] = {'candidate': candidate, 'current_static_references': list(refs),
                      'historical_references_require_review': list(historical)}
    for label, doc in artifacts:
        if not isinstance(doc, dict) or not isinstance(doc.get('rows'), list):
            raise ValueError('invalid classification artifact')
        seen = set()
        for entry in doc['rows']:
            candidate = entry['candidate']
            path = candidate['path']
            if (path in seen or path not in rows or candidate.get('sha256') != rows[path]['candidate']['sha256']
                    or any(f not in candidate or candidate[f] != rows[path]['candidate'][f] for f in FIELDS)):
                raise ValueError('duplicate, unknown or stale classification')
            seen.add(path)
            if label in rows[path]['current_static_references']:
                raise ValueError('duplicate classification label')
            rows[path]['current_static_references'].append(label)
    return [{'candidate': r['candidate'], 'current_static_references': sorted(r['current_static_references']),
             'historical_references_require_review': sorted(r['historical_references_require_review']),
             'status': 'referenced-static-only' if r['current_static_references'] else 'no-supplied-current-reference'}
            for _, r in sorted(rows.items())]


def main():
    if len(sys.argv) < 3:
        print('usage: reference_index_extend.py INDEX.json CLASSIFICATION.json...', file=sys.stderr)
        return 2
    try:
        files = [Path(x) for x in sys.argv[1:]]
        if len({str(p.resolve()) for p in files}) != len(files):
            raise ValueError('duplicate input artifact')
        raws = [p.read_bytes() for p in files]
        docs = [json.loads(raw) for raw in raws]
        for artifact in docs[1:]:
            if artifact.get('input_sha256') != digest(raws[0]):
                raise ValueError('classification input digest mismatch')
        rows = extend(docs[0], [(str(p.resolve()), d) for p, d in zip(files[1:], docs[1:])])
        referenced = sum(bool(r['current_static_references']) for r in rows)
        print(json.dumps({'status':'static-reference-index-not-execution-acceptance', 'snapshot_head':docs[0]['snapshot_head'],
            'limitations':'supplied snapshot and artifacts only; references do not resolve execution; ignored/generated inputs, later changes and runtime are not covered',
            'inputs':[{'path':str(p.resolve()), 'sha256':digest(raw)} for p, raw in zip(files, raws)],
            'total':len(rows), 'referenced':referenced, 'unreferenced':len(rows)-referenced,
            'historical_reference_review':sum(bool(r['historical_references_require_review']) for r in rows),
            'overlap':sum(len(r['current_static_references'])>1 for r in rows), 'rows':rows}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'reference index extension unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
