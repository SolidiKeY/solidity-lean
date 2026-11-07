#!/usr/bin/env python3
"""Reduce bounded KernelInventory logs to frozen hashes and generated API deltas.

Bulk Expr records stay in the supplied evidence directory, outside Git.
This performs no Lean work and does not modify original modules.
"""
import argparse
import hashlib
import json
from pathlib import Path


def reduce(evidence):
    census = json.loads((evidence / 'census.json').read_text())
    expected_modules = {'Solidity.SolcValidation.' + name for name in
                        ['Dialect', 'DataLayout', 'DataResolution']}
    if {path[:-5].replace('/', '.') for path in census['modules']} != expected_modules:
        raise RuntimeError('census does not cover the frozen three-module scope')
    if sum(len(row['declarations']) for row in census['modules'].values()) != 33:
        raise RuntimeError('census does not cover all 33 explicit declarations')
    rows = {}
    for lane in ['old', 'new']:
        result = json.loads((evidence / f'{lane}-KernelInventory-final.json').read_text())
        if result['exit'] != 0 or result['resource_stop']:
            raise RuntimeError(f'{lane} inventory did not pass')
        inventory = {}
        counts = {}
        for line in (evidence / f'{lane}-KernelInventory-final.log').read_text().splitlines():
            if line.startswith('MIGRATION_KERNEL '):
                row = json.loads(line[len('MIGRATION_KERNEL '):])
                if row['name'] in inventory:
                    raise RuntimeError(f'duplicate kernel declaration {row["name"]}')
                inventory[row['name']] = row
            elif line.startswith('MIGRATION_KERNEL_COUNT '):
                _, module, count = line.split()
                if module in counts:
                    raise RuntimeError(f'duplicate module count for {module}')
                counts[module] = int(count)
        if set(counts) != expected_modules or sum(counts.values()) != len(inventory):
            raise RuntimeError(f'incomplete {lane} module inventory')
        for module, count in counts.items():
            if sum(row['module'] == module for row in inventory.values()) != count:
                raise RuntimeError(f'wrong row count for {module}')
        rows[lane] = inventory
    explicit = {}
    for path, module in census['modules'].items():
        for declaration in module['declarations']:
            name = 'Solidity.SolcValidation.' + declaration['name']
            if declaration['private']:
                name = '_private.' + path[:-5].replace('/', '.') + '.0.' + name
            left, right = (rows[lane][name] for lane in ['old', 'new'])
            if left != right:
                raise RuntimeError(f'explicit frozen kernel record differs: {name}')
            explicit[name] = {
                'type_expr_sha256': hashlib.sha256(left['type_expr'].encode()).hexdigest(),
                'record_sha256': hashlib.sha256(json.dumps(
                    left, sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
                'kind': left['kind'], 'axioms': left['axioms']}
    old, new = rows['old'], rows['new']
    changed = {}
    for name in sorted(old.keys() & new.keys()):
        fields = [key for key in sorted(old[name].keys() | new[name].keys())
                  if old[name].get(key) != new[name].get(key)]
        if fields:
            changed[name] = {'changed_fields': fields, 'old_axioms': old[name]['axioms'],
                             'new_axioms': new[name]['axioms']}
    report = {
        'explicit_declarations': explicit, 'explicit_count': len(explicit),
        'explicit_records_identical': True,
        'loaded_constant_counts': {lane: len(data) for lane, data in rows.items()},
        'removed_generated_names': sorted(old.keys() - new.keys()),
        'added_generated_names': sorted(new.keys() - old.keys()),
        'changed_generated_records': changed,
        'boundary': 'Inventories cover imported constants present at command enumeration, '
                    'including available generated declarations, not every possible lazy '
                    'realization. Raw Expr equality is verified for all 33 explicit originals. '
                    'Generated type/axiom differences are reported, not waived. Frozen '
                    'complete source bytes separately attest unchanged definitions.'}
    for lane, data in rows.items():
        (evidence / f'{lane}-kernel-inventory.json').write_text(
            json.dumps(data, indent=2, sort_keys=True) + '\n')
    (evidence / 'frozen-interface-hashes.json').write_text(
        json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(f'PASS: {len(explicit)} explicit kernel records match; '
          f'{len(changed)} common generated records differ')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--evidence', type=Path, required=True)
    reduce(parser.parse_args().evidence)
