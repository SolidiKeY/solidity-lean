#!/usr/bin/env python3
"""Guard regression: later compiler refutations are counted as ordinary witnesses."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import census
import mapping

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'tests/h62/item2/audit-evm-compiler/'
ROLES = {
    'EntryAudit': 'selected joint compiler input from existing nonempty allocation/internal-call certificate',
    'InputFixture': 'correlated input fixtures derived from existing closed public certificates, not global producer inhabitation',
    'JointFromCertificate': 'exact joint tuple from a closed certificate; unresolved data is rejected',
    'JointRefutation': 'terminal-False refutation packages; intentionality is separately justified',
    'RefutationAudit': 'selected intentional refutation classifications, not positive joint witnesses',
    'SelectorAudit': 'five selected ordinary equivalence interfaces with actual input fixtures, not totality statements',
}


def classify(rows):
    if not isinstance(rows, list):
        raise ValueError('invalid mapped census')
    out, seen, other = [], set(), []
    for row in rows:
        path = row['path']
        if not path.startswith(PREFIX):
            continue
        filename = path[len(PREFIX):]
        name = filename[:-5] if filename.endswith('.lean') else ''
        if name not in ROLES:
            other.append(path)
            continue
        if path in seen or row['resolution'] != 'file-check-review':
            raise ValueError('duplicate or unexpected candidate context')
        seen.add(path)
        out.append({'candidate': row, 'role': ROLES[name],
                    'driver': 'enroll_audits.py parses prior Entry/Refutation/Selector receipts and is not a Lean runner; current per-file invocation unresolved',
                    'inputs': 'source/import closure, private evidence and exact current toolchain/cache; current inputs unverified',
                    'effects': 'direct file output not established; audit scripts may write evidence and registry data',
                    'expected_outcome': 'current execution unresolved; intentional refutations do not establish inhabited witnesses',
                    'status': 'static-reference-not-execution-acceptance'})
    if seen != {PREFIX + n + '.lean' for n in ROLES}:
        raise ValueError('missing expected later candidate')
    return out, sorted(other)


def main():
    if len(sys.argv) != 1:
        print('usage: evm_compiler_later_controls.py', file=sys.stderr)
        return 2
    try:
        before = subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip()
        subprocess.run(['git','diff','--quiet','HEAD','--','*.lean'], cwd=ROOT, check=True)
        mapped = mapping.derive(census.census(ROOT))
        subprocess.run(['git','diff','--quiet','HEAD','--','*.lean'], cwd=ROOT, check=True)
        after = subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip()
        if before != after:
            raise ValueError('HEAD changed during scan')
        rows, other = classify(mapped)
        print(json.dumps({'status':'partial-static-classification-not-acceptance', 'head':before,
            'census_sha256':hashlib.sha256((ROOT/'scripts/h55/module-times/census.py').read_bytes()).hexdigest(),
            'mapper_sha256':hashlib.sha256((ROOT/'scripts/h55/module-times/mapping.py').read_bytes()).hexdigest(),
            'limitations':'non-atomic index/worktree scan; ignored/generated paths, index flags, runtime and actual invocation unverified',
            'other_group_paths_not_classified_here':other, 'rows':rows}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        print(f'later EVM compiler classification unavailable: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
