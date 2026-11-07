#!/usr/bin/env python3
"""Report current-family additions while refusing any change to frozen files.

This deliberately does not replace strict frozen accept.py or prove semantics.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
from census import BASE, ROOT, inventory


def compare(frozen, current):
    original = {row['path']: row['sha256'] for row in frozen['files']}
    actual = {row['path']: row['sha256'] for row in current['files']}
    removed = sorted(original.keys() - actual.keys())
    changed = sorted(path for path in original.keys() & actual.keys()
                     if original[path] != actual[path])
    added = sorted(actual.keys() - original.keys())
    return {'schema_version': 1, 'base': BASE,
            'original_file_count': len(original), 'current_file_count': len(actual),
            'original_declaration_count': len(frozen['declarations']),
            'current_declaration_count': len(current['declarations']),
            'original_integrity': 'pass' if not removed and not changed else 'fail',
            'removed': removed, 'changed': changed, 'added': added,
            'added_declarations': [row for row in current['declarations'] if row['path'] in added],
            'boundary': 'Source integrity and addition census only; not frozen acceptance, elaboration or correspondence.'}


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    if output == ROOT or ROOT in output.parents:
        parser.error('bulk output must remain outside the repository')
    frozen = inventory(ROOT, BASE)
    current = inventory(ROOT)
    report = compare(frozen, current)
    report['head'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    encoded = (json.dumps(current, ensure_ascii=False, indent=2) + '\n').encode()
    report['current_inventory_sha256'] = hashlib.sha256(encoded).hexdigest()
    output.parent.mkdir(parents=True, exist_ok=True)
    inventory_path = output.with_name(output.stem + '-inventory.json')
    inventory_path.write_bytes(encoded)
    report['current_inventory_path'] = str(inventory_path)
    output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(f"{report['original_integrity'].upper()}: original file integrity; "
          f"{len(report['added'])} added files; {report['current_declaration_count']} current declarations")
    print(report['boundary'])
    return 0 if report['original_integrity'] == 'pass' else 1


if __name__ == '__main__':
    raise SystemExit(main())
