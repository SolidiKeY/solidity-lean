#!/usr/bin/env python3
"""Compare H55 Lean declaration inventories, permitting only four moved helpers."""
import argparse
import json
import pathlib
import sys

MODULES = tuple('Solidity.Lowering.V08.' + name + 'Controls' for name in
                ('Handler', 'LibraryHandler', 'CreationSuccess', 'Prefix'))
EXPECTED_REMOVED = {(m, f'_private.{m}.0.{m}.extract_failure') for m in MODULES}


def load(path):
    rows = [json.loads(line.removeprefix('H55_DECL ')) for line in pathlib.Path(path).read_text().splitlines()
            if line.startswith('H55_DECL ')]
    result = {(row['module'], row['name']): row for row in rows}
    if not rows or len(result) != len(rows) or {row['module'] for row in rows} != set(MODULES):
        raise ValueError('empty, duplicate, or incomplete module inventory')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('baseline')
    parser.add_argument('changed')
    args = parser.parse_args()
    before, after = load(args.baseline), load(args.changed)
    removed = before.keys() - after.keys()
    added = after.keys() - before.keys()
    changed = [key for key in before.keys() & after.keys() if before[key] != after[key]]
    print(f'baseline={len(before)} changed={len(after)} removed={len(removed)} added={len(added)} modified={len(changed)}')
    for key in sorted(removed): print('removed:', *key)
    for key in sorted(added): print('added:', *key)
    for key in sorted(changed): print('modified:', *key)
    return int(removed != EXPECTED_REMOVED or bool(added) or bool(changed))


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(f'invalid inventory: {error}', file=sys.stderr)
        sys.exit(2)
