"""Self-tests for additive census fragments.

Each sorted *.json file has schema_version 1 and optional routes,
catalog_extensions, roles and fixtures. Route and catalog-extension values
are objects of expanded catalog sections; roles and fixtures are record lists.
Definitions retain their existing validation and classification boundaries.
"""
import json
import tempfile
from pathlib import Path


def fragment_controls(classifier):
    import copy
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
        # JSON booleans and numbers compare equal in Python but are distinct claims.
        try: merge_fragment_entries('standalone', [dict(first, entry_line=1)], [dict(first, entry_line=True)])
        except ValueError: pass
        else: raise AssertionError('boolean/number conflict accepted')
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
