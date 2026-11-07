#!/usr/bin/env python3
"""Report current-family additions while refusing any change to frozen files.

This deliberately does not replace strict frozen accept.py or prove semantics.
"""
import argparse
from collections import Counter
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
    # Preserve multiplicity: nested namespaces can repeat a written name.
    def header_key(row):
        return (row['path'], row['kind'], row['name'], row['statement_sha256'])
    before = Counter(map(header_key, frozen['declarations']))
    after = Counter(map(header_key, current['declarations']))
    def rows(counter):
        return [dict(path=key[0], kind=key[1], name=key[2],
                     statement_sha256=key[3], count=count)
                for key, count in sorted(counter.items())]
    missing_headers = before - after
    additional_headers = after - before
    return {'schema_version': 1, 'base': BASE,
            'original_file_count': len(original), 'current_file_count': len(actual),
            'original_declaration_count': len(frozen['declarations']),
            'current_declaration_count': len(current['declarations']),
            'original_integrity': 'pass' if not removed and not changed else 'fail',
            'removed': removed, 'changed': changed, 'added': added,
            'missing_original_header_count': sum(missing_headers.values()),
            'missing_original_headers': rows(missing_headers),
            'additional_current_header_count': sum(additional_headers.values()),
            'additional_current_headers': rows(additional_headers),
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
    original_path = output.with_name(output.stem + '-original-inventory.json')
    original_encoded = (json.dumps(frozen, ensure_ascii=False, indent=2) + '\n').encode()
    original_path.write_bytes(original_encoded)
    report['original_inventory_path'] = str(original_path)
    report['original_inventory_sha256'] = hashlib.sha256(original_encoded).hexdigest()
    report['current_inventory_path'] = str(inventory_path)
    output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(f"{report['original_integrity'].upper()}: original file integrity; "
          f"{len(report['added'])} added files; {report['current_declaration_count']} current declarations")
    print(report['boundary'])
    return 0 if report['original_integrity'] == 'pass' else 1


if __name__ == '__main__':
    raise SystemExit(main())
