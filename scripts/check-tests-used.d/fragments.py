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


def fragment_controls():
    import copy
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


