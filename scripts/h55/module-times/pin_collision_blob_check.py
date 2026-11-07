#!/usr/bin/env python3
"""Guard regression: pin collision spans are attributed to different source bytes."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import pin_collision_report

ROOT = Path(__file__).resolve().parents[3]


def check_rows(proposal, report, read_source):
    candidates = {}
    for row in proposal['rows']:
        key = row['old_checker_key']
        if not isinstance(key, str) or key in candidates:
            raise ValueError('invalid or duplicate old key')
        candidates[key] = row
    seen, result = set(), []
    for group in report['rows']:
        for selected in group['source_rows']:
            key = selected['old_checker_key']
            if key in seen or key not in candidates:
                raise ValueError('duplicate or unknown collision occurrence')
            seen.add(key)
            row = candidates[key]
            if row['suggested_new_key'] != group['suggested_key'] or any(selected[k] != row[k] for k in selected):
                raise ValueError('collision row differs from proposal')
            source = read_source(row['file'])
            if hashlib.sha256(source).hexdigest() != row['source_sha256']:
                raise ValueError('source blob hash mismatch')
            start, end = row['start_byte'], row['end_byte']
            if type(start) is not int or type(end) is not int or not 0 <= start < end <= len(source):
                raise ValueError('invalid byte span')
            block = row['observed_block'].encode('utf-8')
            if source[start:end] != block or hashlib.sha256(block).hexdigest() != row['block_sha256']:
                raise ValueError('source span mismatch')
            result.append({'old_checker_key': key, 'file': row['file'], 'source_sha256': row['source_sha256'],
                           'start_byte': start, 'end_byte': end, 'block_sha256': row['block_sha256']})
    if len(result) != report['colliding_occurrences'] or len(report['rows']) != report['collision_groups']:
        raise ValueError('collision report counts differ')
    return result


def main():
    if len(sys.argv) != 3:
        print('usage: pin_collision_blob_check.py PROPOSAL.json REPORT.json', file=sys.stderr)
        return 2
    try:
        proposal_raw, report_raw = (Path(x).read_bytes() for x in sys.argv[1:])
        proposal, report = json.loads(proposal_raw), json.loads(report_raw)
        if hashlib.sha256(proposal_raw).hexdigest() != report['proposal_sha256']:
            raise ValueError('proposal digest mismatch')
        if report['rows'] != pin_collision_report.report(proposal):
            raise ValueError('collision report is incomplete or differs from proposal')
        rev = proposal['source_head_unverified']
        if not isinstance(rev, str) or not re.fullmatch(r'[0-9a-f]{40}', rev):
            raise ValueError('invalid source commit')
        subprocess.run(['git', 'cat-file', '-e', rev+'^{commit}'], cwd=ROOT, check=True)
        cache = {}
        def read_source(path):
            if not isinstance(path, str) or not path or PurePosixPath(path).is_absolute() or any(x in ('', '.', '..') for x in path.split('/')):
                raise ValueError('invalid source path')
            if path not in cache:
                entry = subprocess.check_output(['git', 'ls-tree', '-z', rev, '--', path], cwd=ROOT)
                parts = entry.split(b'\0')
                if len(parts) != 2 or parts[-1] != b'' or b'\t' not in parts[0]:
                    raise ValueError('missing or ambiguous tree entry')
                header, actual = parts[0].split(b'\t', 1)
                mode, kind, oid = header.decode('ascii').split()
                if actual.decode('utf-8') != path or kind != 'blob' or mode not in ('100644', '100755'):
                    raise ValueError('not an exact regular source blob')
                cache[path] = subprocess.check_output(['git', 'cat-file', 'blob', oid], cwd=ROOT)
            return cache[path]
        rows = check_rows(proposal, report, read_source)
        print(json.dumps({'status': 'historical-blob-span-check-not-migration', 'source_head': rev,
                          'proposal_sha256': hashlib.sha256(proposal_raw).hexdigest(),
                          'report_sha256': hashlib.sha256(report_raw).hexdigest(),
                          'occurrences': len(rows), 'source_files': len(cache), 'rows': rows,
                          'limitations': 'checks supplied collision occurrences only; Lean resolution, imports, context, ownership and multiplicity migration remain unproved'}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        print(f'pin collision blob check unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
