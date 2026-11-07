#!/usr/bin/env python3
"""Expose non-theorem lexical signals omitted by the theorem-only snapshot.

Every keyword occurrence is retained, including possible false positives. This is
an audit worklist, never a complete declaration inventory or witness acceptance.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
from census import frozen_blobs, mask

KINDS = ('def', 'abbrev', 'opaque', 'axiom', 'constant', 'constants',
         'structure', 'class', 'inductive', 'coinductive', 'instance',
         'example', 'theorem', 'lemma')
PATTERN = re.compile(r'(?<![\w.])(' + '|'.join(KINDS) + r')(?![\w\'₀-₉])')


def signals(source):
    return [dict(keyword=m.group(), offset=m.start(),
                 line=source.count('\n', 0, m.start()) + 1,
                 status='PENDING_LEXICAL_SIGNAL')
            for m in PATTERN.finditer(mask(source))]


def collect(repo, snapshot):
    frozen = frozen_blobs(repo)
    modules = snapshot['modules']
    paths = [m['file'] for m in modules]
    if len(set(paths)) != len(paths):
        raise ValueError('Duplicate snapshot module')
    rows = []
    for module in modules:
        path = module['file']
        if path not in frozen:
            raise ValueError('Unknown frozen module: ' + path)
        blob = frozen[path]
        data = subprocess.check_output(['git', 'cat-file', 'blob', blob], cwd=repo)
        digest = hashlib.sha256(data).hexdigest()
        if digest != module['sha256']:
            raise ValueError('Snapshot/frozen blob mismatch: ' + path)
        found = signals(data.decode())
        rows.append(dict(file=path, blob=blob, sha256=digest, signals=found))
    counts = Counter(s['keyword'] for row in rows for s in row['signals'])
    return dict(status='LEXICAL_WORKLIST_ONLY', modules=rows,
                keyword_counts=dict(sorted(counts.items())),
                module_count=len(rows), new_witnesses=0, fidelity_acceptances=0,
                complete_interface_inventory=False,
                limitations=['Keywords may be syntax quotations or false positives.',
                             'Generated declarations, proof fields, inherited binders and namespace semantics require kernel inventory.',
                             'Frozen snapshot blobs only; current-source validation is not claimed.'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--snapshot', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    repo, out = args.repo.resolve(), args.out.resolve()
    if out == repo or repo in out.parents:
        raise ValueError('Bulk output must remain outside the repository')
    raw = args.snapshot.read_bytes()
    result = collect(repo, json.loads(raw))
    result['snapshot_sha256'] = hashlib.sha256(raw).hexdigest()
    with out.open('x') as handle:
        json.dump(result, handle, indent=2, sort_keys=True)
        handle.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'modules'}, sort_keys=True))


if __name__ == '__main__':
    main()
