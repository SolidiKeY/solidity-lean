#!/usr/bin/env python3
"""Guard regression: colliding proposed pin destinations silently drop occurrences."""
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import sys


def report(data):
    if not isinstance(data, dict) or not isinstance(data.get('rows'), list):
        raise ValueError('invalid dry-run proposal')
    groups, old_keys = defaultdict(list), set()
    for row in data['rows']:
        if not isinstance(row, dict):
            raise ValueError('invalid row')
        old, suggested = row['old_checker_key'], row['suggested_new_key']
        block, expected = row['observed_block'], row['block_sha256']
        if not isinstance(old, str) or not old or old in old_keys:
            raise ValueError('duplicate or invalid old key')
        if not isinstance(suggested, str) or not suggested or not isinstance(block, str):
            raise ValueError('invalid suggested key or block')
        if hashlib.sha256(block.encode('utf-8')).hexdigest() != expected:
            raise ValueError('observed block hash mismatch')
        old_keys.add(old)
        groups[suggested].append(row)
    collisions = {key: rows for key, rows in groups.items() if len(rows) > 1}
    declared = data['duplicate_suggested_keys']
    if not isinstance(declared, list) or len({x[0] for x in declared}) != len(declared):
        raise ValueError('invalid declared collision list')
    if {key: len(rows) for key, rows in collisions.items()} != dict(declared):
        raise ValueError('declared collisions differ from rows')
    if data.get('occurrences') != len(data['rows']) or data.get('duplicate_checker_keys') != []:
        raise ValueError('proposal count or old-key status mismatch')
    result = []
    for key, rows in sorted(collisions.items()):
        result.append({'suggested_key': key, 'occurrences': len(rows),
            'distinct_targets': len({r['target'] for r in rows}),
            'distinct_blocks': len({r['block_sha256'] for r in rows}),
            'distinct_axiom_lists': len({tuple(r['axioms']) for r in rows}),
            'source_rows': [{k: r[k] for k in ('file', 'source_sha256', 'old_checker_key', 'target', 'axioms', 'block_sha256', 'start_byte', 'end_byte')} for r in rows],
            'status': 'all-occurrences-require-context-and-multiplicity-review'})
    return result


def main():
    if len(sys.argv) != 2:
        print('usage: pin_collision_report.py PROPOSAL.json', file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_bytes()
        data = json.loads(raw)
        rows = report(data)
        areas = Counter(r['suggested_key'].split(':', 1)[0] for r in rows)
        print(json.dumps({'status': 'historical-parser-observation-not-migration',
            'proposal_sha256': hashlib.sha256(raw).hexdigest(), 'source_head_unverified': data['source_head_unverified'],
            'limitations': 'suggested key and parsed text are not Lean resolution, owner scope, import context or permission to deduplicate; historical snapshot only',
            'collision_groups': len(rows), 'colliding_occurrences': sum(r['occurrences'] for r in rows),
            'destination_counts': dict(sorted(areas.items())), 'rows': rows}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as exc:
        print(f'pin collision report unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
