#!/usr/bin/env python3
"""Export unverified deletion candidates for two exact guard spellings.

Output is for review and proof checking only, not authorization to apply.
"""
import argparse
import difflib
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
FORMS = {
    'first | (simp only;done) | decide | omega | rfl | skip',
    'first | (simp only;done) | (decide) | omega | rfl | skip',
}


def candidates(name, data):
    lines = data.splitlines(keepends=True)
    found = [i for i, line in enumerate(lines) if line.strip() in FORMS]
    result = [line for i, line in enumerate(lines) if i not in set(found)]
    patch = ''.join(difflib.unified_diff(lines, result, fromfile='a/' + name,
                                          tofile='b/' + name, n=3))
    return found, patch


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('output', type=Path, help='new output directory')
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    names = subprocess.check_output(['git', 'ls-files', '-z', '--', '*.lean'], cwd=ROOT).decode().split('\0')
    rows = []
    for name in sorted(filter(None, names)):
        raw = (ROOT / name).read_bytes()
        found, patch = candidates(name, raw.decode('utf-8'))
        if not found:
            continue
        patch_name = f'{len(rows):04d}.patch'
        patch_data = patch.encode('utf-8')
        (args.output / patch_name).write_bytes(patch_data)
        rows.append({'path': name, 'source_sha256': hashlib.sha256(raw).hexdigest(),
                     'lines': [i + 1 for i in found], 'patch': patch_name,
                     'patch_sha256': hashlib.sha256(patch_data).hexdigest(),
                     'proof_status': 'unverified', 'owner': None})
    manifest = {'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                'tracked_status': subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=ROOT, text=True),
                'scope': 'two exact standalone single-line spellings only; not a complete first/skip census',
                'warning': 'Unverified candidate patches; do not apply without owner agreement and Lean proof checks.',
                'occurrences': sum(len(row['lines']) for row in rows), 'files': rows}
    (args.output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(f"{manifest['occurrences']} candidates in {len(rows)} files")


if __name__ == '__main__':
    main()
