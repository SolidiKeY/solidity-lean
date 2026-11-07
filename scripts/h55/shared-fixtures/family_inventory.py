#!/usr/bin/env python3
"""Inventory lexical family signals in every baseline Lean file in four areas."""
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[3]
BASE = '4d3790eadb8a5212233bc7d5e345817476b2f590'
AREAS = ('Solidity/Lowering/V08', 'Solidity/Backend/StorageOps',
         'Solidity/Lowering/StorageOps', 'Solidity/Lowering/G19')
PATTERNS = {
    'extract_failure': r'\bextract_failure\b',
    'fitting': r'\bfitting\b',
    'uint_syntax': r'\buintSyntax\b',
    'initial': r'\binitial\w*\b',
    'frame': r'\bframe\w*\b',
    'source_execution': r'\b(?:execS|evalE)\b',
    'static': r'\bstatic\b',
    'storage_delete': r'\b(?:deleteStor|delete|deleted|clear)\w*\b',
    'storage_copy': r'\b(?:copy|copied)\w*\b',
    'primitive_kind': r'\b(?:Bool|Int|Signed|bool|int|signed)\b',
    'declaration': r'^\s*(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*(?:theorem|lemma|def|abbrev|example|instance|inductive|structure|class|opaque)\b',
    'case_branch': r'^\s*\|',
}
compiled = {name: re.compile(pattern) for name, pattern in PATTERNS.items()}
paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE, '--', *AREAS], cwd=ROOT, text=True).splitlines()
rows = []
for path in sorted(p for p in paths if p.endswith('.lean')):
    data = subprocess.check_output(['git', 'show', f'{BASE}:{path}'], cwd=ROOT)
    hits = {name: [] for name in compiled}
    for number, line in enumerate(data.decode('utf-8').splitlines(), 1):
        for name, pattern in compiled.items():
            if pattern.search(line):
                hits[name].append(number)
    rows.append({'path': path, 'sha256': hashlib.sha256(data).hexdigest(),
                 'lines': len(data.decode('utf-8').splitlines()), 'hits': hits})
print(json.dumps({'base': BASE, 'patterns': PATTERNS, 'files': rows,
                  'limitation': 'Lexical signals include comments and omit synonyms and multi-line semantic relationships; review all original declarations and cases.'}, sort_keys=True))
