#!/usr/bin/env python3
"""Exercise failure boundaries of the migration audit; never invokes Lean.

All tampered evidence is isolated off Git. Valid logs must pass; failed gates,
missing declarations, changed axiom dependencies and duplicate module counts
must fail even when other evidence is well formed.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys


def check(evidence, output):
    output.mkdir(parents=True, exist_ok=False)
    reducer = Path(__file__).with_name('reduce-inventory.py')
    required = ['census.json'] + [f'{lane}-KernelInventory-final.{suffix}'
                for lane in ['old', 'new'] for suffix in ['json', 'log']]
    outcomes = []
    for case in ['valid', 'failed_gate', 'removed_explicit', 'added_axiom', 'duplicate_count']:
        dest = output / case
        dest.mkdir()
        for name in required:
            shutil.copyfile(evidence / name, dest / name)
        if case == 'failed_gate':
            path = dest / 'new-KernelInventory-final.json'
            result = json.loads(path.read_text())
            result['exit'] = 1
            path.write_text(json.dumps(result))
        elif case == 'removed_explicit':
            # Remove the same explicit declaration from both logs and repair
            # counts, so parity and module counts alone cannot accept it.
            for lane in ['old', 'new']:
                path = dest / f'{lane}-KernelInventory-final.log'
                lines = []
                removed = 0
                for line in path.read_text().splitlines():
                    if line.startswith('MIGRATION_KERNEL '):
                        row = json.loads(line[len('MIGRATION_KERNEL '):])
                        if row['name'] == 'Solidity.SolcValidation.mode_distinct':
                            removed += 1
                            continue
                    if line.startswith('MIGRATION_KERNEL_COUNT Solidity.SolcValidation.Dialect '):
                        fields = line.split()
                        fields[-1] = str(int(fields[-1]) - 1)
                        line = ' '.join(fields)
                    lines.append(line)
                if removed != 1:
                    raise RuntimeError('control failed to remove its target')
                path.write_text('\n'.join(lines) + '\n')
        elif case == 'added_axiom':
            path = dest / 'new-KernelInventory-final.log'
            lines = []
            changed = 0
            for line in path.read_text().splitlines():
                if line.startswith('MIGRATION_KERNEL '):
                    row = json.loads(line[len('MIGRATION_KERNEL '):])
                    if row['name'] == 'Solidity.SolcValidation.mode_distinct':
                        row['axioms'] = ['Classical.choice']
                        line = 'MIGRATION_KERNEL ' + json.dumps(row)
                        changed += 1
                lines.append(line)
            if changed != 1:
                raise RuntimeError('control failed to change its target')
            path.write_text('\n'.join(lines) + '\n')
        elif case == 'duplicate_count':
            path = dest / 'new-KernelInventory-final.log'
            text = path.read_text()
            marker = next(line for line in text.splitlines() if line.startswith('MIGRATION_KERNEL_COUNT '))
            path.write_text(text + marker + '\n')
        result = subprocess.run([sys.executable, str(reducer), '--evidence', str(dest)],
                                capture_output=True, text=True)
        (dest / 'reducer.log').write_text(result.stdout + result.stderr)
        expected_success = case == 'valid'
        if (result.returncode == 0) != expected_success:
            raise RuntimeError(f'control {case} returned {result.returncode}')
        outcomes.append({'case': case, 'exit': result.returncode,
                         'expected_success': expected_success, 'pass': True})
    (output / 'results.json').write_text(json.dumps(outcomes, indent=2) + '\n')
    print('PASS: valid inventory accepted; all four tampered evidence controls rejected')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    check(args.evidence, args.output)
