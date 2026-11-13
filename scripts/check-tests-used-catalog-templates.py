#!/usr/bin/env python3
"""Additive catalog format: shared pinned templates and ordered revision groups.

Frozen v1 and v2 remain independently runnable. This opt-in driver changes
storage only; classification, positive observations and mandatory completeness
are delegated unchanged to v1. Use --ref REV --write/--check, or --self-test.
"""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('tests_used_extension', HERE / 'check-tests-used-catalog-extension.py')
v2 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v2)
v1 = v2.v1
SECTIONS = {'standalone', 'module_entries', 'reads', 'generators', 'orphans'}


def nonfinite(value):
    raise ValueError('nonfinite JSON constant: ' + value)


def parse(raw):
    return json.loads(raw, object_pairs_hook=v1.unique_json_object, parse_constant=nonfinite)


def revision(value):
    return isinstance(value, str) and re.fullmatch('[0-9a-f]{40}', value) is not None


def sha(value):
    return isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value) is not None


def expand(raw, data):
    if not isinstance(data, dict) or set(data) != {'schema_version', 'base_sha256', 'expanded_sha256', 'templates', 'append'}:
        raise ValueError('invalid template catalog fields')
    if type(data['schema_version']) is not int or data['schema_version'] != 3:
        raise ValueError('invalid template catalog version')
    if not sha(data['base_sha256']) or not sha(data['expanded_sha256']):
        raise ValueError('invalid catalog digest')
    if v2.hashlib.sha256(raw).hexdigest() != data['base_sha256']:
        raise ValueError('frozen base digest mismatch')
    base = parse(raw)
    result = copy.deepcopy(base)
    tables, additions = data['templates'], data['append']
    if not isinstance(tables, dict) or not isinstance(additions, dict) or set(tables) != set(additions) or not set(tables) <= SECTIONS:
        raise ValueError('invalid template sections')
    for section, table in tables.items():
        if not isinstance(table, list) or not isinstance(additions[section], list):
            raise ValueError('template tables and groups must be lists')
        entries = []
        for item in table:
            if not isinstance(item, dict): raise ValueError('invalid template')
            if set(item) == {'base_index', 'base_entry_sha256'}:
                index = item['base_index']
                if type(index) is not int or not 0 <= index < len(base[section]):
                    raise ValueError('invalid frozen template index')
                entry = base[section][index]
                if not sha(item['base_entry_sha256']) or v2.digest(entry) != item['base_entry_sha256']:
                    raise ValueError('frozen template digest mismatch')
                if not isinstance(entry, dict) or not revision(entry.get('input_revision')):
                    raise ValueError('frozen template lacks revision')
                entry = {k: copy.deepcopy(v) for k, v in entry.items() if k != 'input_revision'}
            elif set(item) == {'entry'}:
                if not isinstance(item['entry'], dict) or 'input_revision' in item['entry']:
                    raise ValueError('literal template must be revisionless')
                entry = copy.deepcopy(item['entry'])
            else: raise ValueError('invalid template fields')
            entries.append(entry)
        used = set()
        for group in additions[section]:
            if not isinstance(group, dict) or set(group) != {'input_revision', 'template_indices'}:
                raise ValueError('invalid revision group fields')
            if not revision(group['input_revision']) or not isinstance(group['template_indices'], list) or not group['template_indices']:
                raise ValueError('invalid revision group')
            for index in group['template_indices']:
                if type(index) is not int or not 0 <= index < len(entries):
                    raise ValueError('invalid template reference')
                used.add(index)
                entry = copy.deepcopy(entries[index])
                entry['input_revision'] = group['input_revision']
                result[section].append(entry)
        if used != set(range(len(entries))):
            raise ValueError('unused template')
    if v2.digest(result) != data['expanded_sha256']:
        raise ValueError('expanded catalog digest mismatch')
    return result


def encode(raw, catalog):
    """Re-runnable lossless encoding; no new claims or classifications inferred."""
    base = parse(raw)
    if not isinstance(catalog, dict) or set(catalog) != set(base):
        raise ValueError('catalog/base fields differ')
    data = dict(schema_version=3, base_sha256=v2.hashlib.sha256(raw).hexdigest(),
                expanded_sha256=v2.digest(catalog), templates={}, append={})
    def identity(entry):
        return v2.digest({k: v for k, v in entry.items() if k != 'input_revision'})
    for section, original in base.items():
        current = catalog[section]
        if not isinstance(original, list):
            if v2.digest(current) != v2.digest(original): raise ValueError('base scalar changed')
            continue
        if not isinstance(current, list) or v2.digest(current[:len(original)]) != v2.digest(original):
            raise ValueError('frozen prefix changed')
        suffix = current[len(original):]
        if not suffix: continue
        if section not in SECTIONS: raise ValueError('unsupported appended section')
        lookup = {identity(e): i for i, e in enumerate(original)}
        table, groups, indices = [], [], {}
        for entry in suffix:
            if not isinstance(entry, dict) or not revision(entry.get('input_revision')):
                raise ValueError('appended entry lacks revision')
            key = identity(entry)
            if key not in indices:
                index = lookup.get(key)
                if index is None:
                    template = {'entry': {k: copy.deepcopy(v) for k, v in entry.items() if k != 'input_revision'}}
                else:
                    template = dict(base_index=index, base_entry_sha256=v2.digest(original[index]))
                indices[key] = len(table)
                table.append(template)
            if not groups or groups[-1]['input_revision'] != entry['input_revision']:
                groups.append(dict(input_revision=entry['input_revision'], template_indices=[]))
            groups[-1]['template_indices'].append(indices[key])
        data['templates'][section], data['append'][section] = table, groups
    if v2.digest(expand(raw, data)) != v2.digest(catalog):
        raise ValueError('catalog roundtrip differs')
    return data


def load_catalog():
    return expand((HERE / 'check-tests-used-routes.json').read_bytes(),
                  parse((HERE / 'check-tests-used-catalog-templates.json').read_bytes()))


def controls():
    base = dict(schema_version=3, standalone=[dict(path='tests/__catalog_case__.py', input_revision='a' * 40, nested=[1])],
                module_entries=[], reads=[], generators=[], orphans=[])
    raw = json.dumps(base).encode()
    full = copy.deepcopy(base)
    full['standalone'].extend([dict(base['standalone'][0], input_revision='b' * 40),
                               dict(path='tests/__catalog_other__.py', input_revision='b' * 40, nested=[2]),
                               dict(base['standalone'][0], input_revision='c' * 40)])
    good = encode(raw, full)
    assert expand(raw, good) == full
    out = expand(raw, good)
    out['standalone'][1]['nested'].append(9)
    assert out['standalone'][0]['nested'] == out['standalone'][3]['nested'] == [1]
    mutations = []
    def bad(path, value):
        changed = copy.deepcopy(good)
        target = changed
        for key in path[:-1]: target = target[key]
        target[path[-1]] = value
        mutations.append(changed)
    for field, value in [('schema_version', True), ('schema_version', 2), ('extra', 0),
                         ('base_sha256', '0' * 64), ('expanded_sha256', '0' * 64),
                         ('templates', []), ('append', []), ('append', {'unknown': []})]:
        bad([field], value)
    for value in [True, 0.0, -1, 1, '0']:
        bad(['templates', 'standalone', 0, 'base_index'], value)
    bad(['templates', 'standalone', 0, 'base_entry_sha256'], '0' * 64)
    bad(['templates', 'standalone', 1, 'entry', 'input_revision'], 'b' * 40)
    bad(['templates', 'standalone', 0, 'extra'], 0)
    for value in [True, 0.0, -1, 2, '0']:
        bad(['append', 'standalone', 0, 'template_indices', 0], value)
    for value in ['HEAD', True, 'b' * 39]: bad(['append', 'standalone', 0, 'input_revision'], value)
    bad(['append', 'standalone', 0, 'extra'], 0)
    bad(['append', 'standalone', 0, 'template_indices'], [])
    for reverse in ['groups', 'indices', 'omit']:
        changed = copy.deepcopy(good)
        if reverse == 'groups': changed['append']['standalone'].reverse()
        elif reverse == 'indices': changed['append']['standalone'][0]['template_indices'].reverse()
        else: changed['append']['standalone'].pop()
        mutations.append(changed)
    unused = copy.deepcopy(good)
    unused['templates']['standalone'].append({'entry': {'path': 'unused'}})
    mutations.append(unused)
    for changed in mutations:
        try: expand(raw, changed)
        except (ValueError, TypeError, KeyError): pass
        else: raise AssertionError('accepted malformed template catalog')
    for malformed in ['{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}']:
        try: parse(malformed)
        except ValueError: pass
        else: raise AssertionError('accepted ambiguous JSON')
    load_catalog()
    print('PASS catalog template controls')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ref', default='origin/master')
    modes = parser.add_mutually_exclusive_group(required=True)
    for mode in ['write', 'check', 'self-test']: modes.add_argument('--' + mode, action='store_true')
    args = parser.parse_args()
    try:
        if args.self_test:
            controls()
            v2.controls()
            v1.self_test()
            return 0
        root = v1.decode(v1.git(Path.cwd(), 'rev-parse', '--show-toplevel')).strip()
        expected = v1.inventory(v1.Repository(root, args.ref), load_catalog())
        target = Path(root) / v1.OUTPUT
        if args.write: target.write_bytes(v1.output_json(expected))
        else:
            actual = parse(target.read_bytes())
            v1.verify(actual, expected)
            if target.read_bytes() != v1.output_json(expected): raise ValueError('noncanonical inventory bytes')
        print(json.dumps(expected['totals'], sort_keys=True))
        if expected['totals']['unresolved'] or expected['analysis_gaps']:
            print('INCOMPLETE: unresolved paths are not justified classes; no pruning authorization.', file=sys.stderr)
            return 1
        return 0
    except (ValueError, OSError, KeyError, TypeError, AssertionError) as error:
        print('tests-used-templates: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
