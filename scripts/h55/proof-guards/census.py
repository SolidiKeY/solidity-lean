#!/usr/bin/env python3
"""Inventory single-line first/skip candidates; this does not prove no-op status."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[3]
paths = subprocess.check_output(['git', 'ls-files', '-z', '--', '*.lean'], cwd=root).decode().split('\0')
pattern = re.compile(r'\bfirst\s*\|.*\|\s*skip\b')
rows = []
for name in sorted(filter(None, paths)):
    data = (root / name).read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    for number, line in enumerate(data.decode('utf-8').splitlines(), 1):
        if pattern.search(line):
            rows.append({'path': name, 'line': number, 'file_sha256': digest,
                         'text': line.strip(), 'classification': 'unverified'})
print(json.dumps({'base': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
                  'tracked_status': subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=root, text=True),
                  'scope': 'tracked Lean files; single-line lexical candidates only',
                  'warning': 'Includes effective closers, comments and strings; excludes multiline guards. No deletion is authorized by this inventory.',
                  'count': len(rows), 'candidates': rows}, indent=2))
