#!/usr/bin/env python3
"""Produce a baseline theorem inventory for selected storage near-copy pairs.

This is lexical and does not determine Lean namespaces, theorem types, or case
semantics. Whole-file hashes and source-line spans allow independent review.
"""
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[3]
BASE = '4d3790eadb8a5212233bc7d5e345817476b2f590'
AREA = 'Solidity/Lowering/StorageOps/'
PAIRS = {
    'array_delete_bool_int': ('SourceBoolArrayDeleteNumericControls.lean', 'SourceIntArrayDeleteNumericControls.lean'),
    'dynamic_copy_bool_signed': ('SourceBoolStorageCopyTargetControls.lean', 'SourceSignedStorageCopyTargetControls.lean'),
    'fixed_copy_bool': ('SourceBoolFixedStorageCopyControls.lean', 'SourceBoolFixedStorageCopyTargetControls.lean'),
}
DECL = re.compile(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|example)\s+([^\s(:{\[]+)')


def snapshot(name):
    path = AREA + name
    data = subprocess.check_output(['git', 'show', f'{BASE}:{path}'], cwd=ROOT)
    lines = data.decode('utf-8').splitlines(keepends=True)
    starts = [(i, m.group(1), m.group(2)) for i, line in enumerate(lines) if (m := DECL.match(line))]
    declarations = []
    for index, (start, kind, label) in enumerate(starts):
        end = starts[index + 1][0] if index + 1 < len(starts) else len(lines)
        block = ''.join(lines[start:end]).encode()
        declarations.append({'kind': kind, 'name': label, 'lines': [start + 1, end],
                             'sha256': hashlib.sha256(block).hexdigest()})
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'line_count': len(lines),
            'declarations': declarations}


def main():
    pairs = {}
    for label, (left, right) in PAIRS.items():
        a, b = snapshot(left), snapshot(right)
        left_theorems = {d['name'] for d in a['declarations'] if d['kind'] in ('theorem', 'lemma')}
        right_theorems = {d['name'] for d in b['declarations'] if d['kind'] in ('theorem', 'lemma')}
        pairs[label] = {'left': a, 'right': b, 'left_only_theorems': sorted(left_theorems-right_theorems),
                        'right_only_theorems': sorted(right_theorems-left_theorems),
                        'shared_theorem_names': sorted(left_theorems & right_theorems)}
    print(json.dumps({'base': BASE, 'pairs': pairs,
                      'limitation': 'Lexical declaration starts; names need not have the same namespace, type, cases, or meaning. Hashes include following text through the next recognized declaration.'}, sort_keys=True))


if __name__ == '__main__':
    main()
