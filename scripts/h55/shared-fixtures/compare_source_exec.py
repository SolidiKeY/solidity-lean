#!/usr/bin/env python3
"""Fail-closed comparison of the pinned Source-execution kernel inventories."""
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
MODULES = set((ROOT / 'tests/h55/shared-fixtures/source-exec-modules.txt').read_text().splitlines())
FIELDS = {'module', 'name', 'typeExpr', 'levelParams', 'valueExpr', 'axioms',
          'theorem', 'unsafe', 'partial', 'axiom'}


def load(directory, baseline=False):
    files = sorted(pathlib.Path(directory).glob('Batch*.jsonl'))
    if len(files) != 10:
        raise ValueError('expected ten audit batches')
    rows = {}
    for file in files:
        for line in file.read_text().splitlines():
            if not line.startswith('H55_DECL '):
                continue
            row = json.loads(line.removeprefix('H55_DECL '))
            if set(row) != FIELDS or (row['theorem'] and row['valueExpr'] is not None):
                raise ValueError('invalid record schema')
            key = (row['module'], row['name'])
            if key in rows:
                raise ValueError('duplicate declaration')
            rows[key] = row
    if {key[0] for key in rows} != MODULES or (baseline and len(rows) != 3103):
        raise ValueError('missing module or incomplete pinned baseline')
    return rows


def differences(before, after):
    removed = sorted(before.keys() - after.keys())
    added = sorted(after.keys() - before.keys())
    modified = sorted(key for key in before.keys() & after.keys() if before[key] != after[key])
    unsafe_added = [key for key in added if any(after[key][flag] for flag in ('unsafe', 'partial', 'axiom'))]
    return removed, added, modified, unsafe_added


def main():
    if len(sys.argv) != 3:
        raise ValueError('usage: compare_source_exec.py BASELINE_DIR CHANGED_DIR')
    before, after = load(sys.argv[1], baseline=True), load(sys.argv[2])
    removed, added, modified, unsafe_added = differences(before, after)
    print(f'baseline={len(before)} changed={len(after)} removed={len(removed)} added={len(added)} modified={len(modified)} unsafe_added={len(unsafe_added)}')
    for label, keys in (('removed', removed), ('added', added), ('modified', modified), ('unsafe_added', unsafe_added)):
        for key in keys:
            print(label + ':', *key)
    return int(bool(removed or modified or unsafe_added))


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(f'invalid inventory: {error}', file=sys.stderr)
        sys.exit(2)
