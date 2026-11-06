"""Guard uncovered/matched partition swaps, omitted names and unpinned source metadata.

Metadata consistency only: a source-name match supplies no hypothesis witness.
Historical witness sublabels are permitted, never validated as witnesses or endorsed.
The caller must supply an independently authenticated source-census SHA256.
"""
import hashlib
import json
import math
import re


def strict_json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError('duplicate JSON key')
            result[key] = value
        return result
    def constant(value):
        raise ValueError('nonfinite JSON constant')
    def floating(value):
        result = float(value)
        if not math.isfinite(result):
            raise ValueError('nonfinite JSON number')
        return result
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=constant,
                      parse_float=floating)


def canonical(value):
    return json.dumps(value, sort_keys=True, allow_nan=False, separators=(',', ':'))


def indexed(rows):
    if not isinstance(rows, list):
        raise ValueError('declaration array required')
    result = {}
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError('declaration object required')
        for field in ('name', 'module', 'signature', 'kernel_type_expr'):
            if not isinstance(row.get(field), str) or not row[field]:
                raise ValueError('missing declaration identity')
        if row['name'] in result:
            raise ValueError('duplicate declaration name')
        result[row['name']] = row
    return result


def partition(raw_rows, annotated_rows, source_bytes, expected_source_sha256):
    if not isinstance(expected_source_sha256, str) or not re.fullmatch('[0-9a-f]{64}', expected_source_sha256):
        raise ValueError('independent source digest required')
    if hashlib.sha256(source_bytes).hexdigest() != expected_source_sha256:
        raise ValueError('source census digest drift')
    source = strict_json(source_bytes)
    if not isinstance(source, dict) or not isinstance(source.get('declarations'), list):
        raise ValueError('source declaration array required')
    names = set()
    for row in source['declarations']:
        if not isinstance(row, dict) or 'name_candidate' not in row:
            raise ValueError('source candidate required')
        name = row['name_candidate']
        if name is not None and (not isinstance(name, str) or not name):
            raise ValueError('invalid source candidate')
        if name is not None:
            names.add(name)
    raw, annotated = indexed(raw_rows), indexed(annotated_rows)
    if raw.keys() != annotated.keys():
        raise ValueError('complete declaration name sets differ')
    uncovered = sorted(raw.keys() - names)
    for name, original in raw.items():
        saved = annotated[name]
        if any(key not in saved or canonical(saved[key]) != canonical(value)
               for key, value in original.items()):
            raise ValueError('saved kernel field drift')
        coverage = saved.get('coverage')
        if coverage not in ('named_source_h70_witness', 'named_source_prior_witness', 'uncovered_compiler_declaration'):
            raise ValueError('unknown coverage annotation')
        if (coverage == 'uncovered_compiler_declaration') != (name not in names):
            raise ValueError('coverage partition drift')
    return {'uncovered': uncovered, 'source_name_matches': sorted(raw.keys() & names),
            'kernelValidated': False, 'witnesses_added': 0, 'releaseClosed': False}


def partition_pinned(raw_bytes, annotated_bytes, source_bytes, pins):
    """Guard coordinated compiler/annotation drift behind independent input pins.

    Pins must come from an authenticated external inventory. Matching bytes do
    not establish that a compiler ran or that its historical proof passed.
    """
    roles = {'compiler': raw_bytes, 'annotations': annotated_bytes, 'source': source_bytes}
    if not isinstance(pins, dict) or pins.keys() != roles.keys():
        raise ValueError('exact three-role digest inventory required')
    for role, data in roles.items():
        pin = pins[role]
        if not isinstance(data, bytes):
            raise ValueError('raw bytes required')
        if not isinstance(pin, str) or not re.fullmatch('[0-9a-f]{64}', pin):
            raise ValueError('independent input digest required')
        if hashlib.sha256(data).hexdigest() != pin:
            raise ValueError(role + ' digest drift')
    return partition(strict_json(raw_bytes), strict_json(annotated_bytes),
                     source_bytes, pins['source'])


MAX_INPUT_BYTES = 16 * 1024 * 1024


def read_input(path):
    """Reject nonregular/oversized metadata before reading it into memory."""
    import os
    import stat
    descriptor = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
    with os.fdopen(descriptor, 'rb') as stream:
        info = os.fstat(stream.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_size > MAX_INPUT_BYTES:
            raise ValueError('regular metadata input within 16 MiB required')
        data = stream.read(MAX_INPUT_BYTES + 1)
        if len(data) > MAX_INPUT_BYTES:
            raise ValueError('metadata input grew beyond 16 MiB')
        return data


def main(argv=None):
    """Reproduce metadata comparison without executing any producer or proof."""
    import argparse
    from pathlib import Path
    import sys
    parser = argparse.ArgumentParser(description=__doc__)
    for role in ('compiler', 'annotations', 'source'):
        parser.add_argument('--' + role, type=Path, required=True)
        parser.add_argument('--' + role + '-sha256', required=True)
    args = parser.parse_args(argv)
    try:
        roles = ('compiler', 'annotations', 'source')
        data = {role: read_input(getattr(args, role)) for role in roles}
        pins = {role: getattr(args, role + '_sha256') for role in roles}
        result = partition_pinned(data['compiler'], data['annotations'], data['source'], pins)
    except (OSError, ValueError, TypeError, RecursionError) as error:
        print('CENSUS_METADATA_REJECT: ' + str(error), file=sys.stderr)
        return 2
    print(json.dumps(result, sort_keys=True, allow_nan=False))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
