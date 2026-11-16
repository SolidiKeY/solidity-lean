#!/usr/bin/env python3
"""Opt-in append-only catalog v2. Classification and completeness remain v1.

Use --ref REV --write/--check, or --self-test. Frozen v1 remains independently
runnable with its historical catalog. No new observation interface is added.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('tests_used_v1', HERE / 'check-tests-used.py')
v1 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v1)


def digest(value):
    return hashlib.sha256((json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()).hexdigest()


def expand(raw, delta):
    if not isinstance(delta, dict) or set(delta) != {'schema_version', 'base_sha256', 'expanded_sha256', 'append'}:
        raise ValueError('invalid delta fields')
    if type(delta['schema_version']) is not int or delta['schema_version'] != 2:
        raise ValueError('invalid delta version')
    for field in ('base_sha256', 'expanded_sha256'):
        if not isinstance(delta[field], str) or not re.fullmatch('[0-9a-f]{64}', delta[field]):
            raise ValueError('invalid digest')
    if hashlib.sha256(raw).hexdigest() != delta['base_sha256']:
        raise ValueError('frozen base digest mismatch')
    base = json.loads(raw, object_pairs_hook=v1.unique_json_object)
    result = copy.deepcopy(base)
    additions = delta['append']
    if not isinstance(additions, dict) or not set(additions) <= {'standalone', 'reads', 'module_entries', 'generators', 'orphans'}:
        raise ValueError('invalid append sections')
    for section, entries in additions.items():
        if not isinstance(entries, list): raise ValueError('append section must be a list')
        for item in entries:
            if not isinstance(item, dict): raise ValueError('invalid entry')
            if set(item) == {'entry'}:
                if not isinstance(item['entry'], dict): raise ValueError('invalid literal entry')
                entry = copy.deepcopy(item['entry'])
            elif set(item) == {'base_index', 'base_entry_sha256', 'input_revision'}:
                index = item['base_index']
                if type(index) is not int or not 0 <= index < len(base[section]):
                    raise ValueError('invalid base index')
                entry = copy.deepcopy(base[section][index])
                if digest(entry) != item['base_entry_sha256']: raise ValueError('entry digest mismatch')
                revision = item['input_revision']
                if 'input_revision' not in entry or not isinstance(revision, str) or not re.fullmatch('[0-9a-f]{40}', revision):
                    raise ValueError('invalid revision')
                entry['input_revision'] = revision
            else: raise ValueError('invalid entry fields')
            result[section].append(entry)
    if digest(result) != delta['expanded_sha256']: raise ValueError('expanded digest mismatch')
    return result


def load_catalog():
    return expand((HERE / 'check-tests-used-routes.json').read_bytes(),
                  json.loads((HERE / 'check-tests-used-catalog-extension.json').read_bytes(),
                             object_pairs_hook=v1.unique_json_object))


def controls():
    base = {'standalone': [{'input_revision': 'a' * 40, 'nested': [1]}]}
    raw = json.dumps(base).encode()
    expected = copy.deepcopy(base)
    expected['standalone'].append({'input_revision': 'b' * 40, 'nested': [1]})
    good = {'schema_version': 2, 'base_sha256': hashlib.sha256(raw).hexdigest(),
            'expanded_sha256': digest(expected), 'append': {'standalone': [
                {'base_index': 0, 'base_entry_sha256': digest(base['standalone'][0]), 'input_revision': 'b' * 40}]}}
    assert expand(raw, good) == expected
    out = expand(raw, good)
    out['standalone'][1]['nested'].append(2)
    assert out['standalone'][0]['nested'] == [1]
    mutations = []
    def bad(path, value):
        changed = copy.deepcopy(good)
        target = changed
        for key in path[:-1]: target = target[key]
        target[path[-1]] = value
        mutations.append(changed)
    for field, value in (('schema_version', True), ('schema_version', 1), ('base_sha256', '0' * 64),
                         ('expanded_sha256', '0' * 64), ('extra', 1), ('append', []), ('append', {'unknown': []})):
        bad([field], value)
    for field, values in (('base_index', [True, -1, 1, '0']), ('input_revision', ['HEAD', True, 'b' * 39]),
                          ('base_entry_sha256', ['0' * 64]), ('extra', [1])):
        for value in values: bad(['append', 'standalone', 0, field], value)
    for value in (None, [], {'entry': []}, {'entry': {}, 'base_index': 0}):
        bad(['append', 'standalone', 0], value)
    for changed in mutations:
        try: expand(raw, changed)
        except (ValueError, TypeError, KeyError): pass
        else: raise AssertionError('accepted malformed delta')
    literal = copy.deepcopy(good)
    literal['append']['standalone'] = [{'entry': expected['standalone'][1]}]
    assert expand(raw, literal) == expected
    # Order and frozen entries are provenance, even for literal additions.
    ordered = copy.deepcopy(good)
    ordered['append']['standalone'] = [{'entry': {'label': 'first'}},
                                       {'entry': {'label': 'second'}}]
    ordered_expected = copy.deepcopy(base)
    ordered_expected['standalone'].extend([{'label': 'first'}, {'label': 'second'}])
    ordered['expanded_sha256'] = digest(ordered_expected)
    assert expand(raw, ordered) == ordered_expected
    reversed_entries = copy.deepcopy(ordered)
    reversed_entries['append']['standalone'].reverse()
    omitted_entry = copy.deepcopy(ordered)
    omitted_entry['append']['standalone'].pop()
    for changed in (reversed_entries, omitted_entry):
        try: expand(raw, changed)
        except ValueError: pass
        else: raise AssertionError('accepted reordered or missing provenance')
    load_catalog()
    print('PASS v2 catalog controls')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ref', default='origin/master')
    modes = parser.add_mutually_exclusive_group(required=True)
    for mode in ('write', 'check', 'self-test'): modes.add_argument('--' + mode, action='store_true')
    args = parser.parse_args()
    try:
        if args.self_test:
            controls()
            v1.self_test()
            return 0
        root = v1.decode(v1.git(Path.cwd(), 'rev-parse', '--show-toplevel')).strip()
        expected = v1.inventory(v1.Repository(root, args.ref), load_catalog())
        target = Path(root) / v1.OUTPUT
        if args.write: target.write_bytes(v1.output_json(expected))
        else:
            actual = json.loads(target.read_bytes(), object_pairs_hook=v1.unique_json_object)
            v1.verify(actual, expected)
            if target.read_bytes() != v1.output_json(expected): raise ValueError('noncanonical inventory bytes')
        print(json.dumps(expected['totals'], sort_keys=True))
        if expected['totals']['unresolved'] or expected['analysis_gaps']:
            print('INCOMPLETE: unresolved paths are not justified classes; no pruning authorization.', file=sys.stderr)
            return 1
        return 0
    except (ValueError, OSError, KeyError, TypeError, AssertionError) as error:
        print('tests-used-v2: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
