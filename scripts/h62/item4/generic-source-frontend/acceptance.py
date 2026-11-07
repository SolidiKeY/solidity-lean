#!/usr/bin/env python3
"""Static reproducibility acceptance; never implies runtime/migration PASS.

--full requires the real fixture closure and table outputs, matched timings,
owner approval/application and full run-lean final gate. It fails closed while
any are absent. No goal status/permission is inferred from this report.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
from census import BASE, inventory, encode
from generate import REPO, generated


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
    diff = subprocess.check_output(['git', 'diff', BASE, '--', 'Solidity/Frontend'], cwd=REPO)
    if diff:
        raise SystemExit('OWNED_ORIGINAL_CHANGED')
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
                  frozen_originals_changed=0,
                  boundary='source inventory/reproduction only; not elaborated-statement or semantic proof validation',
                  blockers=[{'id':'B-MIGRATION-TOKEN','type':'producer_dependency',
                             'file':'Solidity/Frontend/Checked/Token.lean:38',
                             'owner':'solidity-h62-6-20261106/migrate-frontend',
                             'reason':'pinned Lean4.35 String constructor mismatch; actual FixtureData closure fails'},
                            {'id':'B-OWNER','type':'owner_agreement',
                             'reason':'exact-file owner relay approval/application and module registration absent'},
                            {'id':'B-WORDTABLE','type':'implementation_pending',
                             'reason':'439 numeric prefix proofs preserved/inventoried; generic consolidation unproved'},
                            {'id':'B-FULL-GATES','type':'validation_pending',
                             'reason':'table/adapters, full affected run-lean, elaborated statement/trust inventory and matched timing pending'}])
    args.output.write_text(encode(report))
    print(encode(report))
    if args.full:
        raise SystemExit('FULL_ACCEPTANCE_BLOCKED: required proofs, producer, owner and timing gates outstanding')

if __name__ == '__main__':
    main()
