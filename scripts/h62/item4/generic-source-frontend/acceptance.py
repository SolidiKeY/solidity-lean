#!/usr/bin/env python3
"""Static reproducibility acceptance; never implies runtime/migration PASS.

--full requires the real fixture closure and table outputs, matched timings,
owner approval/application and full run-lean final gate. It fails closed while
any are absent. No goal status/permission is inferred from this report.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
import subprocess
from census import BASE, inventory, encode
from generate import REPO, generated


ANNOTATION = b'-- H55 reproduction: scripts/h55/vectors-tables/word_table.py (proof text remains authoritative).\n'


def allowed_source_delta(path, frozen, current):
    """Allow only the exact H82 annotation; preserve every original code byte."""
    if frozen == current:
        return False
    if not re.fullmatch(r'Solidity/Frontend/NumericLiteralProofs/WordTable/Part[0-2][0-9]\.lean', path):
        raise SystemExit('OWNED_ORIGINAL_CHANGED: ' + path)
    first, separator, remainder = frozen.partition(b'\n')
    if not separator or not first.startswith(b'import ') or ANNOTATION in frozen:
        raise SystemExit('INVALID_ANNOTATION_BASE: ' + path)
    if current != first + separator + ANNOTATION + remainder:
        raise SystemExit('PROOF_TEXT_CHANGED: ' + path)
    return True



def check_changed_paths(raw, untracked):
    """Retain the full Frontend path/status/mode boundary, including non-Lean files."""
    if untracked:
        raise SystemExit('UNTRACKED_FRONTEND_FILE')
    fields = raw.split(b'\0')
    if fields[-1] == b'':
        fields.pop()
    if len(fields) % 2:
        raise SystemExit('MALFORMED_FRONTEND_DIFF')
    for metadata, path in zip(fields[::2], fields[1::2]):
        parts = metadata.split()
        if (len(parts) != 5 or parts[0] != b':100644' or parts[1] != b'100644'
                or parts[4] != b'M' or not re.fullmatch(
                    rb'Solidity/Frontend/NumericLiteralProofs/WordTable/Part[0-2][0-9]\.lean', path)):
            raise SystemExit('FRONTEND_PATH_STATUS_OR_MODE_CHANGED')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--inventory', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--full', action='store_true')
    args = ap.parse_args()
    current = inventory(REPO)
    if args.inventory.read_text() != encode(current):
        raise SystemExit('CENSUS_DRIFT')
    for path, content in generated(REPO).items():
        if (REPO/path).read_text() != content:
            raise SystemExit('GENERATED_DRIFT: ' + str(path))
    subprocess.run(['git', 'merge-base', '--is-ancestor', BASE, 'HEAD'], cwd=REPO, check=True)
    check_changed_paths(
        subprocess.check_output(['git', 'diff', '--raw', '-z', '--no-renames', BASE, '--', 'Solidity/Frontend'], cwd=REPO),
        subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard', '-z', '--', 'Solidity/Frontend'], cwd=REPO))
    annotations = []
    for entry in current['files']:
        path = entry['path']
        frozen = subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=REPO)
        live = (REPO/path).read_bytes()
        if allowed_source_delta(path, frozen, live):
            annotations.append(dict(path=path, frozen_sha256=hashlib.sha256(frozen).hexdigest(),
                                    current_sha256=hashlib.sha256(live).hexdigest()))
    baseline = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE, '--', 'Solidity/Frontend'], cwd=REPO, text=True).splitlines()
    if sorted(x for x in baseline if x.endswith('.lean')) != sorted(f['path'] for f in current['files']):
        raise SystemExit('ORIGINAL_FILE_INVENTORY_CHANGED')
    cases = [f for f in current['files'] if '/FixtureControls/' in f['path']]
    words = [f for f in current['files'] if '/NumericLiteralProofs/WordTable/' in f['path']]
    if (len(cases), sum(len(f['declarations']) for f in cases), len(words), sum(len(f['declarations']) for f in words)) != (45, 45, 30, 439):
        raise SystemExit('AUDIT16_INVENTORY_CHANGED')
    report = dict(status='STATIC_ACCEPTANCE_PASS', runtime_gate_pass=False,
                  base=BASE, inventory_sha256=hashlib.sha256(args.inventory.read_bytes()).hexdigest(),
                  statement_fixture_files=45, statement_fixture_theorems=45,
                  word_table_files=30, word_table_theorems=439,
                  declarations=sum(len(f['declarations']) for f in current['files']),
                  frozen_originals_changed=len(annotations),
                  statement_preserving_annotations=annotations,
                  original_code_bytes_preserved=True,
                  boundary='source inventory/reproduction only; not elaborated-statement or semantic proof validation',
                  blockers=[{'id':'B-MIGRATION-TOKEN','type':'producer_dependency',
                             'file':'Solidity/Frontend/Checked/Token.lean:38',
                             'owner':'solidity-h62-6-20261106/migrate-frontend',
                             'reason':'pinned Lean4.35 String constructor mismatch; actual FixtureData closure fails'},
                            {'id':'B-INTEGRATION','type':'validated_owner_integration',
                             'reason':'actual fixture/adaptor integration and registration pending; H82 permission-only waits withdrawn, Claude-owned originals remain read-only'},
                            {'id':'B-WORDTABLE','type':'implementation_pending',
                             'reason':'439 numeric prefix proofs preserved/inventoried; generic consolidation unproved'},
                            {'id':'B-FULL-GATES','type':'validation_pending',
                             'reason':'table/adapters, full affected run-lean, elaborated statement/trust inventory and matched timing pending'}])
    args.output.write_text(encode(report))
    print(encode(report))
    if args.full:
        raise SystemExit('FULL_ACCEPTANCE_BLOCKED: required proofs, producer, integration and timing gates outstanding')

if __name__ == '__main__':
    main()
