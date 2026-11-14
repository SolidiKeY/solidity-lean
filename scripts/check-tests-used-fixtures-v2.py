#!/usr/bin/env python3
"""Opt-in fixture refusals beside the frozen inventory classifiers.

A reviewed exact object can lose an evidence claim when its bytes are regression
input. This never certifies a reader or promotes a class. Positive keep chains,
all existing predicates and the mandatory completeness check stay unchanged.
"""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import sys
import types

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('tests_used_templates', HERE / 'check-tests-used-catalog-templates.py')
templates = importlib.util.module_from_spec(spec)
spec.loader.exec_module(templates)
v1 = templates.v1
DATA = HERE / 'check-tests-used-fixtures-v2.json'


def reviewed_refusals(repo, data):
    if (not isinstance(data, dict) or set(data) != {'schema_version', 'records'}
            or type(data['schema_version']) is not int or data['schema_version'] != 2
            or not isinstance(data['records'], list)):
        raise ValueError('invalid fixture refusal catalog')
    seen = set()
    active = []
    for row in data['records']:
        if not isinstance(row, dict) or set(row) != {'path', 'blob', 'consumers', 'reason'}:
            raise ValueError('invalid fixture refusal record')
        path = row['path']
        if (not isinstance(path, str) or path.startswith('/') or '..' in path.split('/')
                or not path or not v1.hex_pin(row['blob'], 40)
                or not isinstance(row['reason'], str) or not row['reason'].strip()
                or not isinstance(row['consumers'], list) or not row['consumers']):
            raise ValueError('unreviewed fixture refusal')
        if path in seen:
            raise ValueError('duplicate fixture refusal path')
        seen.add(path)
        consumers = set()
        for reader in row['consumers']:
            if (not isinstance(reader, dict) or set(reader) != {'path', 'blob', 'anchors'}
                    or not isinstance(reader['path'], str) or reader['path'] == path
                    or reader['path'].startswith('/') or '..' in reader['path'].split('/')
                    or Path(reader['path']).suffix not in ('.py', '.mjs', '.js', '.cjs', '.sh', '.lean')
                    or not v1.hex_pin(reader['blob'], 40)
                    or not isinstance(reader['anchors'], list) or not reader['anchors']
                    or any(not isinstance(a, str) or not a.strip() or '\n' in a for a in reader['anchors'])
                    or len(set(reader['anchors'])) != len(reader['anchors'])):
                raise ValueError('invalid reviewed fixture consumer')
            if reader['path'] in consumers:
                raise ValueError('duplicate fixture consumer')
            consumers.add(reader['path'])
        if path not in repo.tree:
            continue  # No object exists at this historical input; no claim to refuse.
        if path not in repo.paths or repo.tree[path] != ('100644', 'blob', row['blob']):
            raise ValueError('stale fixture refusal object: ' + path)
        for reader in row['consumers']:
            source = reader['path']
            if repo.tree.get(source) != ('100644', 'blob', reader['blob']):
                raise ValueError('stale fixture consumer object: ' + source)
            if any(a not in repo.texts.get(source, '').splitlines() for a in reader['anchors']):
                raise ValueError('fixture consumer anchor mismatch: ' + source)
        active.append(row)
    return active


def refuse_evidence(repo, original, data):
    """Only withdraw reviewed evidence claims; preserve all positive use claims."""
    records = reviewed_refusals(repo, data)
    output = copy.deepcopy(original)
    by_path = {row['path']: row for row in output['records']}
    for refusal in records:
        row = by_path[refusal['path']]
        if row['class'] != 'evidence':
            continue
        row['class'] = None
        row['reason'] = 'Unresolved regression-fixture role: ' + refusal['reason']
        row['secondary']['reviewed_fixture_refusal'] = copy.deepcopy(refusal)
        row['unresolved'].append('UNRESOLVED_REVIEWED_FIXTURE: historical content does not certify its current regression consumer')
    output['totals'] = {**{c: sum(row['class'] == c for row in output['records']) for c in v1.CLASSES},
                        'paths': len(output['records']),
                        'unresolved': sum(bool(row['unresolved']) for row in output['records'])}
    return output


def inventory(repo, catalog, data=None):
    if data is None:
        data = templates.parse(DATA.read_bytes())
    return refuse_evidence(repo, v1.inventory(repo, catalog), data)


def controls():
    path, reader = 'tests/report.json', 'scripts/test_report.py'
    record = dict(path=path, blob='a' * 40, consumers=[dict(path=reader, blob='b' * 40,
                  anchors=['def test_report():', '    assert exact_bytes'])], reason='Exact bytes are positive and negative regression input; no reader qualification follows.')
    data = dict(schema_version=2, records=[record])
    repo = types.SimpleNamespace(paths=[path], tree={path: ('100644', 'blob', 'a' * 40),
            reader: ('100644', 'blob', 'b' * 40)}, texts={reader: 'def test_report():\n    assert exact_bytes\n'})
    original = dict(schema_version=v1.SCHEMA, measured_revision='c' * 40, analysis_gaps=[],
                    records=[dict(path=path, **{'class': 'evidence'}, reason='Historical report',
                                  secondary={'historical_role': 'Historical report'}, unresolved=[])],
                    totals=dict(paths=1, keep=0, regenerable=0, evidence=1, orphan=0, unresolved=0))
    frozen = copy.deepcopy(original)
    refused = refuse_evidence(repo, original, data)
    assert original == frozen and refused['records'][0]['class'] is None
    assert refused['records'][0]['secondary']['historical_role'] == 'Historical report'
    assert refused['totals']['unresolved'] == 1 and refused['totals']['evidence'] == 0
    assert refuse_evidence(repo, refused, data) == refused
    v1.verify(refused, refused, require_complete=False)
    try:
        v1.verify(refused, refused)
    except ValueError as error:
        assert 'incomplete classification: 1 unresolved paths' in str(error)
    else:
        raise AssertionError('fixture refusal bypassed mandatory completeness')
    for classification in ['keep', 'regenerable', 'orphan', None]:
        current = copy.deepcopy(original)
        current['records'][0]['class'] = classification
        current['records'][0]['unresolved'] = ['unproved'] if classification is None else []
        current['totals'] = {**{c: int(c == classification) for c in v1.CLASSES}, 'paths': 1,
                             'unresolved': int(classification is None)}
        assert refuse_evidence(repo, current, data) == current
    assert refuse_evidence(repo, original, dict(schema_version=2, records=[])) == original
    absent = types.SimpleNamespace(paths=[], tree={}, texts={})
    assert reviewed_refusals(absent, data) == []
    mutations = []
    for key, value in [('schema_version', True), ('schema_version', 1), ('records', {}), ('extra', 0)]:
        bad = copy.deepcopy(data); bad[key] = value; mutations.append(bad)
    for key, value in [('blob', '0'), ('path', '../tests/report.json'), ('reason', ''), ('consumers', [])]:
        bad = copy.deepcopy(data); bad['records'][0][key] = value; mutations.append(bad)
    for key, value in [('path', path), ('path', '../scripts/test.py'), ('blob', '0' * 40),
                       ('anchors', ['missing line']), ('anchors', ['def test_report():\n']), ('anchors', [])]:
        bad = copy.deepcopy(data); bad['records'][0]['consumers'][0][key] = value; mutations.append(bad)
    bad = copy.deepcopy(data); bad['records'] *= 2; mutations.append(bad)
    bad = copy.deepcopy(data); bad['records'][0]['consumers'] *= 2; mutations.append(bad)
    bad = copy.deepcopy(data); bad['records'][0]['blob'] = 'd' * 40; mutations.append(bad)
    for bad in mutations:
        try:
            refuse_evidence(repo, original, bad)
        except (ValueError, TypeError):
            pass
        else:
            raise AssertionError('invalid or stale fixture refusal accepted')
    print('PASS v2 fixture refusal controls: exact objects/consumers/anchors, stale and duplicate refusal, no promotion, positive use preservation, unchanged completeness')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ref', default='origin/master')
    modes = parser.add_mutually_exclusive_group(required=True)
    for mode in ['write', 'check', 'self-test']:
        modes.add_argument('--' + mode, action='store_true')
    args = parser.parse_args()
    try:
        if args.self_test:
            controls()
            templates.controls()
            templates.v2.controls()
            v1.self_test()
            return 0
        root = v1.decode(v1.git(Path.cwd(), 'rev-parse', '--show-toplevel')).strip()
        expected = inventory(v1.Repository(root, args.ref), templates.load_catalog())
        target = Path(root) / v1.OUTPUT
        if args.write:
            target.write_bytes(v1.output_json(expected))
        else:
            actual = templates.parse(target.read_bytes())
            v1.verify(actual, expected)
            if target.read_bytes() != v1.output_json(expected):
                raise ValueError('noncanonical inventory bytes')
        print(json.dumps(expected['totals'], sort_keys=True))
        if expected['totals']['unresolved'] or expected['analysis_gaps']:
            print('INCOMPLETE: unresolved paths are not justified classes; no pruning authorization.', file=sys.stderr)
            return 1
        return 0
    except (ValueError, OSError, KeyError, TypeError, AssertionError) as error:
        print('tests-used-fixtures-v2: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
