#!/usr/bin/env python3
"""Map the exhaustive source inventory to audit 9/11/16 candidates.

Tags are explicitly name/file heuristics, not semantic equivalence or proof
coverage claims. No inventory row is discarded; full-file pins are the
preservation gate. Raw/vector generators are H55-owned and are not generated.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
from census import census, sha

FIXTURES = {'heap_repr', 'allocator', 'represented', 'core', 'refs', 'wide',
            'values', 'heap', 'machine', 'bases', 'old', 'state'}
NEGATIVE = re.compile(r'refus|reject|wrong|bad|overrun|not_|panic|saturat|fail|exhaust|timeout|shadow|unread|invalid|absen')

def audit(inventory):
    rows = []
    helpers = []
    for file in inventory['files']:
        for decl in file['declarations']:
            tags = []
            if 'Path' in Path(file['path']).stem:
                tags.append(9)
            if file['controls'] and decl['name'] in FIXTURES:
                tags.append(11)
                helpers.append((decl['name'], file['path'], decl['line']))
            proof = decl['kind'] in ('theorem', 'lemma')
            if file['controls'] and proof:
                tags.append(16)
            rows.append(dict(path=file['path'], line=decl['line'], name=decl['name'],
                             kind=decl['kind'], header_sha256=decl['header_sha256'],
                             audit_candidates=tags,
                             negative_name_signal=bool(proof and NEGATIVE.search(decl['name']))))
    return dict(schema=1, inventory_sha256=sha((json.dumps(inventory, ensure_ascii=False, indent=2, sort_keys=True)+'\n').encode()),
                boundary='Source inventory and candidate heuristics only; no semantic proof, exclusion, or migration approval.',
                audit_items={9:'Path-labelled family declaration candidates; concrete paths, fresh binds, indexed and alias controls retained.',
                             11:'Repeated intrinsic HeapRepr/AllocatorRepr and singleton-HRef fixture candidates in Controls files.',
                             16:'Controls theorem candidates for typed data tables. No decide-table replacement, no H55 Raw/vector duplication.'},
                counts=dict(inventory_rows=len(rows),
                            negative_name_signals=sum(row['negative_name_signal'] for row in rows),
                            by_audit={str(item):sum(item in row['audit_candidates'] for row in rows) for item in (9,11,16)}),
                repeated_helper_names=dict(sorted(Counter(row[0] for row in helpers).items())),
                rows=rows)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=Path.cwd())
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    report = audit(census(a.root))
    data = (json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True)+'\n').encode()
    a.output.write_bytes(data)
    print(json.dumps(dict(sha256=sha(data), **report['counts']), sort_keys=True))

if __name__ == '__main__':
    main()
