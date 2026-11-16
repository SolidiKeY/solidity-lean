"""Deterministic additive census classification fragments."""
import json
import tempfile
from pathlib import Path


def unique_json_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result: raise ValueError('duplicate JSON object key: ' + key)
        result[key] = value
    return result


def canonical(value):
    return (json.dumps(value, ensure_ascii=True, indent=2, sort_keys=True) + '\n').encode()


# A fragment is an additive object with schema_version 1 and any of routes,
# catalog_extensions, roles and fixtures. Route sections use expanded catalog
# entries; roles and fixtures are lists of the existing record formats. Files
# are read in filename order. Classification validators remain authoritative.
FRAGMENT_SECTIONS = ('standalone', 'generators', 'reads', 'orphans', 'module_entries')


def fragment_identity(section, row):
    if not isinstance(row, dict): raise ValueError('fragment entry must be an object')
    if section in ('roles', 'fixtures'):
        keys = ('path',)
    elif section in ('standalone', 'generators', 'orphans'):
        keys = ('path', 'input_revision')
    elif section in ('module_entries', 'reads'):
        keys = ('runner', 'input_revision', 'target', 'frames')
    else:
        raise ValueError('unknown fragment section')
    if any(k not in row for k in keys): raise ValueError('fragment entry lacks identity: ' + section)
    values = [row[k] for k in keys]
    if section in ('module_entries', 'reads'):
        frames = row['frames']
        if not isinstance(frames, list) or any(not isinstance(f, dict) for f in frames):
            raise ValueError('invalid fragment frames')
        values[-1] = [{k: v for k, v in frame.items() if k != 'blob'} for frame in frames]
    return canonical(values)


def read_fragments(directory):
    result = {key: [] for key in FRAGMENT_SECTIONS + ('roles', 'fixtures')}
    for path in sorted(directory.glob('*.json')):
        document = json.loads(path.read_bytes(), object_pairs_hook=unique_json_object)
        if (not isinstance(document, dict) or type(document.get('schema_version')) is not int
                or document['schema_version'] != 1
                or not set(document) <= {'schema_version', 'routes', 'catalog_extensions', 'roles', 'fixtures'}):
            raise ValueError('invalid classification fragment: ' + str(path))
        for group in ('routes', 'catalog_extensions'):
            sections = document.get(group, {})
            if not isinstance(sections, dict) or not set(sections) <= set(FRAGMENT_SECTIONS):
                raise ValueError('invalid fragment catalog sections: ' + str(path))
            for section, entries in sections.items():
                if not isinstance(entries, list): raise ValueError('fragment section must be a list')
                result[section].extend(entries)
        for section in ('roles', 'fixtures'):
            entries = document.get(section, [])
            if not isinstance(entries, list): raise ValueError('fragment section must be a list')
            result[section].extend(entries)
    return result


def merge_fragment_entries(section, existing, additions):
    # Repeated identical claims are harmless; a different claim for the same
    # identity is ambiguous and rejected, regardless of file order.
    seen = {}
    for row in existing:
        key = fragment_identity(section, row)
        if key in seen and seen[key] != row: raise ValueError('conflicting existing ' + section + ' entries')
        seen[key] = row
    result = list(existing)
    for row in additions:
        key = fragment_identity(section, row)
        if key in seen:
            if seen[key] != row: raise ValueError('conflicting ' + section + ' fragment entries')
            continue
        seen[key] = row
        result.append(row)
    return result


def fragment_controls(classifier):
    import copy
    global read_fragments, merge_fragment_entries
    read_fragments = classifier["read_fragments"]
    merge_fragment_entries = classifier["merge_fragment_entries"]
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        first = {'path': 'tests/a', 'input_revision': 'a' * 40, 'source_blob': 'b' * 40}
        second = {'path': 'tests/b', 'input_revision': 'a' * 40, 'source_blob': 'c' * 40}
        (directory / 'z.json').write_text(json.dumps({'schema_version': 1, 'catalog_extensions': {'standalone': [second]}}))
        (directory / 'a.json').write_text(json.dumps({'schema_version': 1, 'routes': {'standalone': [first]},
                                                        'roles': [{'path': 'tests/note'}],
                                                        'fixtures': [{'path': 'tests/fixture'}]}))
        fragments = read_fragments(directory)
        assert fragments['standalone'] == [first, second]
        assert fragments['roles'][0]['path'] == 'tests/note'
        assert fragments['fixtures'][0]['path'] == 'tests/fixture'
        assert merge_fragment_entries('standalone', [first], [copy.deepcopy(first), second]) == [first, second]
        conflict = dict(first, source_blob='d' * 40)
        try: merge_fragment_entries('standalone', [first], [conflict])
        except ValueError: pass
        else: raise AssertionError('conflicting fragment accepted')
        for invalid in ('{"schema_version":1,"schema_version":1}',
                        '{"schema_version":1,"routes":{"unknown":[]}}',
                        '{"schema_version":1,"roles":{}}'):
            (directory / 'bad.json').write_text(invalid)
            try: read_fragments(directory)
            except ValueError: pass
            else: raise AssertionError('invalid fragment accepted')
        (directory / 'bad.json').unlink()
        assert read_fragments(directory) == fragments



    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp) / 'repo'
        (root / 'tests').mkdir(parents=True)
        runner = 'tests/check.py'
        source = "import unittest\nclass T(unittest.TestCase):\n def test_it(self):\n  open('tests/data.txt').read()\nif __name__ == '__main__': unittest.main()\n"
        (root / runner).write_text(source)
        (root / 'tests/data.txt').write_text('fixture content\n')
        (root / 'tests/note.txt').write_text('reviewed note anchor\n')
        (root / 'tests/receipt.txt').write_text('....\n----------------------------------------------------------------------\nRan 4 tests in 0.001s\n\nOK\n')
        git = classifier['git']
        git(root, 'init', '-q'); git(root, 'add', '.')
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', 'fragment controls')
        repo = classifier['Repository'](root, 'HEAD')
        blob = lambda path: repo.tree[path][2]
        catalog = {'schema_version': 1, 'standalone': [], 'reads': [], 'generators': [], 'orphans': []}
        standalone = {'path': runner, 'input_revision': repo.ref, 'source_blob': blob(runner),
                      'command': ['python3', '-B', runner], 'kind': 'unittest',
                      'purpose': 'Check the named fixture.', 'input_scope': ['tests/data.txt'], 'other_reads': 'unresolved'}
        route = {'runner': 'validated:' + runner, 'input_revision': repo.ref,
                 'frames': [{'path': runner, 'blob': blob(runner), 'line': 4}],
                 'target': 'tests/data.txt', 'target_blob': blob('tests/data.txt'),
                 'operation': 'validated Python read of measured bytes'}
        role = {'path': 'tests/note.txt', 'blob': blob('tests/note.txt'), 'anchor': 'reviewed note anchor',
                'role': 'Historical record: Synthetic reviewed note.'}
        fixture = {'path': 'tests/receipt.txt', 'blob': blob('tests/receipt.txt'),
                   'consumers': [{'path': runner, 'blob': blob(runner), 'anchors': [' def test_it(self):']}],
                   'reason': 'Synthetic receipt is also a regression fixture.'}
        directory = Path(tmp) / 'fragments'; directory.mkdir()
        (directory / 'step.json').write_text(json.dumps({'schema_version': 1, 'routes': {'standalone': [standalone]},
            'catalog_extensions': {'reads': [route]}, 'roles': [role], 'fixtures': [fixture]}))
        original = classifier['read_fragments']
        try:
            classifier['read_fragments'] = lambda _: original(directory)
            model = classifier['inventory'](repo, catalog)
            rows = {r['path']: r for r in model['records']}
            assert rows['tests/data.txt']['class'] == 'keep'
            assert rows['tests/note.txt']['class'] == 'evidence'
            assert rows['tests/receipt.txt']['class'] is None
            assert 'reviewed_fixture_refusal' in rows['tests/receipt.txt']['secondary']
            conflicting = dict(standalone, source_blob='0' * 40)
            (directory / 'other.json').write_text(json.dumps({'schema_version': 1, 'routes': {'standalone': [conflicting]}}))
            try: classifier['inventory'](repo, catalog)
            except ValueError as error: assert 'conflicting' in str(error)
            else: raise AssertionError('end-to-end conflict accepted')
        finally:
            classifier['read_fragments'] = original
