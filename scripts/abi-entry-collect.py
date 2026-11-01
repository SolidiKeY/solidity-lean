#!/usr/bin/env python3
"""Lane CF1: collect before/after runner reports into one results JSON.

Usage: scripts/abi-entry-collect.py BEFORE_DIR AFTER_DIR OUT.json META.json
Each DIR holds <n>/results.json written by scripts/abi-entry-fixtures.sh in
the order of tests/upstream/cf1-abi-entry-fixtures.txt. Observations are kept
in full (hex-encoded byte lists), in order.
"""
import hashlib, json, os, sys

def hexb(xs): return '0x' + bytes(xs).hex() if isinstance(xs, list) else xs

def compact(o):
    if isinstance(o, dict):
        return {k: (hexb(v) if k in ('returnBytes', 'revertBytes', 'calldataBytes', 'calldata', 'expectedBytes')
                    and isinstance(v, list) and all(isinstance(x, int) for x in v) else compact(v))
                for k, v in o.items()}
    if isinstance(o, list): return [compact(x) for x in o]
    return o

def load(d, n):
    p = os.path.join(d, str(n), 'results.json')
    if not os.path.exists(p): return None, None, None
    raw = open(p, 'rb').read()
    rep = json.loads(raw)
    rows = rep['results']
    return rep, (rows[0] if rows else None), hashlib.sha256(raw).hexdigest()

before_dir, after_dir, out, meta = sys.argv[1:5]
paths = [l.strip() for l in open('tests/upstream/cf1-abi-entry-fixtures.txt') if l.strip() and not l.startswith('#')]
fixtures, counts = [], {'before': {}, 'after': {}}
for n, path in enumerate(paths, 1):
    entry = {'path': 'test/libsolidity/semanticTests/' + path}
    for phase, d in (('before', before_dir), ('after', after_dir)):
        got = load(d, n)
        if got[0] is None:
            entry[phase] = None; continue
        rep, row, digest = got
        entry[phase] = {'reportSha256': digest, 'outputDirectory': os.path.join(d, str(n)),
                        'modelSha256': rep['metadata'].get('modelSha256'),
                        'runnerSha256': rep['metadata'].get('runnerSha256'),
                        'result': compact(row)}
        st = row['status'] if row else 'missing'
        counts[phase][st] = counts[phase].get(st, 0) + 1
    fixtures.append(entry)
doc = json.load(open(meta))
doc.update({'counts': counts, 'fixtures': fixtures})
json.dump(doc, open(out, 'w'), indent=1)
print(json.dumps(counts))
