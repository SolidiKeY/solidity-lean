#!/usr/bin/env python3
"""Challenge the actual acceptance entry point using off-git forged inventories.

Original repository sources are read only. No Lean proof acceptance is tested.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT/'scripts/h62/item4/generic-p10'))
import accept


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inventory', required=True, type=Path)
    args = parser.parse_args()
    inventory = json.loads(args.inventory.read_text())
    original_receipt = json.loads((ROOT/'tests/h62/item4/generic-p10/census-receipt.json').read_text())
    cases = [
        ('checksum-tamper', lambda d: d.update(boundary='forged'), False, 'checksum'),
        ('missing-source', lambda d: d['files'].pop(), True, 'file set'),
        ('forged-source-hash', lambda d: d['files'][0].update(source_sha256='0'*64), True, 'unpinned source'),
        ('empty-inventory', lambda d: d.update(files=[]), True, 'file set'),
        ('changed-theorem-statement', lambda d: d['files'][0]['declarations'][0].update(statement='False'), True, 'differs from frozen'),
    ]
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory)
        for name, change, rehash, reason in cases:
            candidate = copy.deepcopy(inventory)
            change(candidate)
            raw = json.dumps(candidate, ensure_ascii=False, indent=2, sort_keys=True).encode()+b'\n'
            receipt = copy.deepcopy(original_receipt)
            if rehash: receipt['inventory_sha256'] = hashlib.sha256(raw).hexdigest()
            (path/'inventory.json').write_bytes(raw)
            (path/'receipt.json').write_text(json.dumps(receipt))
            try:
                accept.verify(ROOT, path/'inventory.json', path/'receipt.json')
            except ValueError as error:
                if reason not in str(error): raise AssertionError((name, str(error))) from error
                print(f'EXPECTED_REFUSAL: {name}: {error}')
            else:
                raise AssertionError(f'forgery accepted: {name}')
    print('NEGATIVE_SOURCE_ACCEPTANCE_PASS: 5 forgeries refused; originals untouched')


if __name__ == '__main__': main()
