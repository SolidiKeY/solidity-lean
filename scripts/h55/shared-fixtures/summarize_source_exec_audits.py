#!/usr/bin/env python3
"""Check batch coverage and summarize a Source-execution kernel census."""
import collections
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
modules = (ROOT / 'tests/h55/shared-fixtures/source-exec-modules.txt').read_text().splitlines()
audit_dir = pathlib.Path(sys.argv[1])
files = sorted(audit_dir.glob('Batch*.jsonl'))
if len(modules) != 74 or len(set(modules)) != 74 or len(files) != 10:
    raise SystemExit('unexpected module or batch count')
rows = []
for file in files:
    for line in file.read_text().splitlines():
        if line.startswith('H55_DECL '):
            rows.append(json.loads(line.removeprefix('H55_DECL ')))
counts = collections.Counter(row['module'] for row in rows)
keys = {(row['module'], row['name']) for row in rows}
if set(counts) != set(modules) or len(keys) != len(rows):
    raise SystemExit('missing module or duplicate declaration')
report = {'modules': len(counts), 'constants': len(rows),
          'theorems': sum(row['theorem'] for row in rows),
          'unsafe': sorted(row['name'] for row in rows if row['unsafe']),
          'partial': sorted(row['name'] for row in rows if row['partial']),
          'axiom_declarations': sorted(row['name'] for row in rows if row['axiom']),
          'counts': dict(sorted(counts.items())),
          'limitation': 'Lexically selected module subset; no cross-version or independent review claim.'}
print(json.dumps(report, indent=2, sort_keys=True))
