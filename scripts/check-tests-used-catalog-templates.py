#!/usr/bin/env python3
"""Additive catalog format: shared pinned templates and ordered revision groups.

Frozen v1 and v2 remain independently runnable. This opt-in driver changes
storage only; classification, positive observations and mandatory completeness
are delegated unchanged to v1. Legacy --write/--check remain available.
H901 --export --artifact PATH writes the current fixture/gzip census outside
Git; --check-manifest --artifact PATH reads its committed identity and SHA256.
Obtain that private artifact from the manifest repository/commit/path. Both
new modes take --ref REV and optional H871 --roles PATH. The additive
gzip_roles catalog field opts in when --roles is absent; explicit --roles
selects its supplied catalog as before. Both use the unchanged landed helper.
The role_delta_proposal locator pins a separately reviewed contract.
The historical_role_delta_manifest locator opts external modes into paired
--historical-role-delta-manifest and --historical-role-delta private files.
Opt-in rebuilds both the base-only and combined models; orphan reviews and
every blocker beyond the eligible path's own generic-use marker fail closed.
In a clone of the proposal repository, check its bytes with
`git show <evidence_commit>:<evidence_path> | sha256sum` against its sha256.
Real-object reviews
remain independently required. A matching SHA256 never replaces rebuilding
the complete model or the unchanged mandatory completeness check.
"""
import argparse
import copy
import importlib.util
import json
import math
from pathlib import Path
import re
import sys
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('tests_used_extension', HERE / 'check-tests-used-catalog-extension.py')
v2 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v2)
v1 = v2.v1
SECTIONS = {'standalone', 'module_entries', 'reads', 'generators', 'orphans'}
MANIFEST_KEY = 'inventory_manifest'
PROPOSAL_KEY = 'role_delta_proposal'
ROLE_DELTA_KEY = 'historical_role_delta_manifest'
GZIP_KEY = 'gzip_roles'  # Explicit opt-in data in the landed H871 schema.
MAX_ARTIFACT_BYTES = 50 * 1024 * 1024  # Existing private-evidence per-file limit.


def nonfinite(value):
    raise ValueError('nonfinite JSON constant: ' + value)


def finite_float(value):
    result = float(value)
    if not math.isfinite(result): raise ValueError('nonfinite JSON number')
    return result


def parse(raw):
    return json.loads(raw, object_pairs_hook=v1.unique_json_object,
                      parse_constant=nonfinite, parse_float=finite_float)


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


def validate_manifest(data):
    fields = {'schema_version', 'input_revision', 'sha256', 'bytes',
              'repository', 'evidence_commit', 'evidence_path'}
    if not isinstance(data, dict) or set(data) != fields:
        raise ValueError('invalid inventory manifest fields')
    if type(data['schema_version']) is not int or data['schema_version'] != 1:
        raise ValueError('invalid inventory manifest version')
    if not revision(data['input_revision']) or not revision(data['evidence_commit']) or not sha(data['sha256']):
        raise ValueError('invalid inventory manifest identity')
    if type(data['bytes']) is not int or not 0 < data['bytes'] <= MAX_ARTIFACT_BYTES:
        raise ValueError('invalid inventory manifest size')
    path = data['evidence_path']
    if (data['repository'] != 'SolidiKeY/solidity-lean-coord'
            or not isinstance(path, str) or not path.startswith('evidence/')
            or any(part in ('', '.', '..') for part in path.split('/'))
            or any(c in path for c in '\0\r\n')):
        raise ValueError('invalid private inventory evidence location')
    return data


def validate_proposal(proposal):
    fields = {'repository', 'evidence_commit', 'evidence_path', 'bytes', 'sha256'}
    if not isinstance(proposal, dict) or set(proposal) != fields:
        raise ValueError('invalid proposal locator fields')
    # Reuse the inventory location, size and digest checks.
    validate_manifest({**proposal, 'schema_version': 1,
               'input_revision': proposal['evidence_commit']})


def catalog_document():
    data = parse((HERE / 'check-tests-used-catalog-templates.json').read_bytes())
    if not isinstance(data, dict):
        raise ValueError('invalid template document')
    if MANIFEST_KEY in data:
        validate_manifest(data[MANIFEST_KEY])
    if PROPOSAL_KEY in data:
        validate_proposal(data[PROPOSAL_KEY])
    if ROLE_DELTA_KEY in data:
        validate_proposal(data[ROLE_DELTA_KEY])
        if PROPOSAL_KEY in data:
            raise ValueError('proposal and role-delta manifest cannot coexist')
    return data


def load_catalog():
    data = {key: value for key, value in catalog_document().items() if key not in {MANIFEST_KEY, GZIP_KEY, PROPOSAL_KEY, ROLE_DELTA_KEY}}
    return expand((HERE / 'check-tests-used-routes.json').read_bytes(), data)


def external_artifact(root, artifact):
    path = Path(artifact).resolve()
    try:
        relative = path.relative_to(Path(root).resolve())
    except ValueError:
        return path
    if v1.git(root, 'ls-files', '--', relative.as_posix()):
        raise ValueError('inventory artifact must be outside Git tracking')
    return path


def write_artifact(root, artifact, raw):
    target = external_artifact(root, artifact)
    target.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=target.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(raw)
        temporary.replace(target)  # Do not overwrite an existing inode through a hardlink.
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def verify_manifest_artifact(root, manifest, expected, artifact):
    validate_manifest(manifest)
    if manifest['input_revision'] != expected['measured_revision']:
        raise ValueError('inventory manifest differs from resolved input revision')
    with external_artifact(root, artifact).open('rb') as stream:
        raw = stream.read(manifest['bytes'] + 1)
    if len(raw) != manifest['bytes'] or v2.hashlib.sha256(raw).hexdigest() != manifest['sha256']:
        raise ValueError('inventory artifact size or SHA256 mismatch')
    actual = parse(raw)
    if raw != v1.output_json(actual):
        raise ValueError('noncanonical manifest inventory bytes')
    v1.verify(actual, expected)  # Full rebuild comparison AND mandatory completeness.


def canonical_private_json(data):
    return (json.dumps(data, indent=2, sort_keys=True) + '\n').encode('utf-8')


def bounded_private_json(root, path, identity):
    with external_artifact(root, path).open('rb') as stream:
        raw = stream.read(identity['bytes'] + 1)
    if len(raw) != identity['bytes'] or v2.hashlib.sha256(raw).hexdigest() != identity['sha256']:
        raise ValueError('role-delta private input size or SHA256 mismatch')
    data = parse(raw)
    if raw != canonical_private_json(data):
        raise ValueError('noncanonical role-delta private input')
    return data


def role_delta_inputs(repo, catalog, document, manifest_path, delta_path):
    locator = document.get(ROLE_DELTA_KEY)
    if locator is None or manifest_path is None or delta_path is None:
        raise ValueError('role-delta locator and both private files are required')
    validate_proposal(locator)
    manifest = bounded_private_json(repo.root, manifest_path, locator)
    fields = {'schema_version', 'input_revision', 'base_sha256', 'sha256',
              'bytes', 'repository', 'evidence_commit', 'evidence_path'}
    if not isinstance(manifest, dict) or set(manifest) != fields:
        raise ValueError('invalid role-delta manifest fields')
    validate_manifest({key: value for key, value in manifest.items() if key != 'base_sha256'})
    base_raw = (HERE / 'check-tests-used-roles.json').read_bytes()
    if (manifest['input_revision'] != repo.ref or not sha(manifest['base_sha256'])
            or manifest['base_sha256'] != v2.hashlib.sha256(base_raw).hexdigest()):
        raise ValueError('role-delta revision or base differs from current inputs')
    delta = bounded_private_json(repo.root, delta_path, manifest)
    # The frozen predicate validates every field, including stale records.
    base = parse(base_raw)
    v1.reviewed_historical_notes(repo, base)
    eligible = v1.reviewed_historical_notes(repo, delta)
    paths = {row['path'] for row in delta['records']}
    if paths & {row['path'] for row in catalog['orphans']}:
        raise ValueError('role-delta path has an orphan review')
    combined = dict(schema_version=1, records=base['records'] + delta['records'])
    v1.reviewed_historical_notes(repo, combined)  # Includes duplicate/overlap refusal.
    return combined, eligible, paths


def guard_role_delta(catalog, baseline, candidate, paths, eligible):
    """Allow only predicate-bound provenance and its own generic-use removal."""
    if paths & {row['path'] for row in catalog['orphans']}:
        raise ValueError('role-delta path has an orphan review')
    if len(candidate['records']) != len(baseline['records']):
        raise ValueError('role-delta changed the inventory universe')
    allowed = copy.deepcopy(baseline)
    marker = 'UNRESOLVED_USE: candidate search is not a certified use graph or proof of non-use'
    for old, new, target in zip(baseline['records'], candidate['records'], allowed['records']):
        path = old['path']
        if path in paths and path in eligible:
            role = eligible[path]
            target['secondary']['historical_role'] = role
            own = (old['class'] is None and new['class'] == 'evidence'
                   and old['unresolved'].count(marker) == 1 and new['reason'] == role)
            if own:
                target['class'] = 'evidence'
                target['unresolved'].remove(marker)
            if own or old['class'] == 'evidence':
                target['reason'] = role
        if canonical_private_json(target) != canonical_private_json(new):
            raise ValueError('role-delta changed a blocker, field, pin or unrelated provenance')
    allowed['totals'] = {**{c: sum(r['class'] == c for r in allowed['records']) for c in v1.CLASSES},
                         'paths': len(allowed['records']),
                         'unresolved': sum(bool(r['unresolved']) for r in allowed['records'])}
    # Full serialized equality also refuses added/dropped header and row fields.
    if canonical_private_json(allowed) != canonical_private_json(candidate):
        raise ValueError('role-delta changed inventory headers, field sets or totals')
    return candidate


def current_inventory(root, ref, roles, role_manifest=None, role_delta=None):
    spec = importlib.util.spec_from_file_location('tests_used_gzip', HERE / 'check-tests-used-gzip.py')
    adapter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(adapter)
    fixtures = adapter.classifier()
    repo = fixtures.v1.Repository(root, ref)
    catalog = fixtures.templates.load_catalog()
    document = catalog_document()
    opted = ROLE_DELTA_KEY in document or role_manifest is not None or role_delta is not None
    inputs = role_delta_inputs(repo, catalog, document, role_manifest, role_delta) if opted else None
    expected = fixtures.inventory(repo, catalog)
    selected = None
    gzip_opted = roles is not None or GZIP_KEY in document
    if gzip_opted:
        selected = parse(roles.read_bytes()) if roles is not None else document[GZIP_KEY]
        expected = adapter.apply_roles(repo, expected, selected)
    if inputs is None:
        return expected
    combined, eligible, paths = inputs
    isolated = adapter.classifier()
    original = isolated.v1.reviewed_historical_notes
    try:
        isolated.v1.reviewed_historical_notes = lambda r, definitions=None: original(
            r, combined if definitions is None else definitions)
        candidate = isolated.inventory(repo, catalog)
    finally:
        isolated.v1.reviewed_historical_notes = original
    if gzip_opted:
        candidate = adapter.apply_roles(repo, candidate, selected)
    return guard_role_delta(catalog, expected, candidate, paths, eligible)


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
    assert parse('{"x":1.25}') == {'x': 1.25}
    for malformed in ['{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}',
                      '{"x":1e999}', '{"x":-1e999}']:
        try: parse(malformed)
        except ValueError: pass
        else: raise AssertionError('accepted ambiguous JSON')
    proposal = catalog_document()[PROPOSAL_KEY]
    validate_proposal(proposal)
    for field, value in [('extra', 0), ('repository', 'wrong'),
                         ('evidence_commit', 'HEAD'), ('evidence_path', 'evidence/../bad'),
                         ('bytes', True), ('sha256', 'bad')]:
        changed = dict(proposal, **{field: value})
        try: validate_proposal(changed)
        except ValueError: pass
        else: raise AssertionError('accepted invalid proposal locator ' + field)
    missing = dict(proposal)
    del missing['evidence_path']
    try: validate_proposal(missing)
    except ValueError: pass
    else: raise AssertionError('accepted incomplete proposal locator')
    load_catalog()
    print('PASS catalog template controls')


def manifest_controls():
    with tempfile.TemporaryDirectory(prefix='tests-used-manifest-controls-') as directory:
        base = Path(directory)
        root = base / 'repository'
        root.mkdir()
        v1.git(root, 'init', '-q')
        artifact = base / 'inventory.json'
        expected = dict(schema_version=v1.SCHEMA, measured_revision='c' * 40,
                        analysis_gaps=[], records=[dict(path='tests/pending.txt', **{'class': None})],
                        totals=dict(paths=1, keep=0, evidence=0, regenerable=0, orphan=0, unresolved=1))
        def pinned(raw):
            artifact.write_bytes(raw)
            return dict(schema_version=1, input_revision='c' * 40, bytes=len(raw),
                        sha256=v2.hashlib.sha256(raw).hexdigest(),
                        repository='SolidiKeY/solidity-lean-coord', evidence_commit='b' * 40,
                        evidence_path='evidence/control/inventory.json')
        manifest = pinned(v1.output_json(expected))
        def refused(record, model, message):
            try:
                verify_manifest_artifact(root, record, model, artifact)
            except ValueError as error:
                assert message in str(error), str(error)
            else:
                raise AssertionError('manifest bypassed original verification')
        refused(manifest, expected, 'incomplete classification: 1 unresolved paths')
        complete = copy.deepcopy(expected)
        complete['records'][0]['class'] = 'keep'
        complete['totals'].update(keep=1, unresolved=0)
        manifest = pinned(v1.output_json(complete))
        verify_manifest_artifact(root, manifest, complete, artifact)
        forged = copy.deepcopy(complete)
        forged['records'][0]['class'] = 'evidence'
        forged['totals'].update(keep=0, evidence=1)
        # Even a correctly re-pinned artifact cannot override the rebuilt model.
        refused(pinned(v1.output_json(forged)), complete, 'classification provenance')
        refused(pinned(json.dumps(complete, indent=2).encode()), complete, 'noncanonical')
        refused(pinned(b'{"schema_version":1,"schema_version":1}'), complete, 'duplicate')
        manifest = pinned(v1.output_json(complete))
        artifact.write_bytes(artifact.read_bytes() + b'x')
        refused(manifest, complete, 'size or SHA256')
        manifest = pinned(v1.output_json(complete))
        wrong = dict(manifest, input_revision='d' * 40)
        refused(wrong, complete, 'resolved input revision')
        wrong = dict(manifest, sha256='0' * 64)
        refused(wrong, complete, 'size or SHA256')
        for field, value in [('schema_version', True), ('schema_version', 2),
                             ('input_revision', 'HEAD'), ('sha256', '0'),
                             ('bytes', True), ('bytes', 0), ('bytes', MAX_ARTIFACT_BYTES + 1),
                             ('repository', 'other/repository'), ('evidence_commit', 'main'),
                             ('evidence_path', '/evidence/file'), ('evidence_path', 'evidence/../file'),
                             ('evidence_path', 'evidence/line\nfile')]:
            try:
                validate_manifest(dict(manifest, **{field: value}))
            except ValueError:
                pass
            else:
                raise AssertionError('invalid manifest accepted: ' + field)
        for change in ['extra', 'missing']:
            invalid = dict(manifest)
            if change == 'extra':
                invalid['extra'] = 0
            else:
                del invalid['evidence_commit']
            try:
                validate_manifest(invalid)
            except ValueError:
                pass
            else:
                raise AssertionError('manifest fields not exact')
        tracked = root / 'tracked.json'
        tracked.write_text('{}')
        v1.git(root, 'add', '--', 'tracked.json')
        try:
            external_artifact(root, tracked)
        except ValueError:
            pass
        else:
            raise AssertionError('manifest mode could overwrite a tracked artifact')
        assert external_artifact(root, root / 'untracked.json') == root / 'untracked.json'
        alias = base / 'outside-hardlink.json'
        alias.hardlink_to(tracked)
        write_artifact(root, alias, b'private replacement')
        assert tracked.read_bytes() == b'{}' and alias.read_bytes() == b'private replacement'
    print('PASS H901 manifest controls: private identity, tamper/re-pin/stale refusal, canonical full-model comparison and mandatory completeness')



def gzip_binding_controls():
    """Exercise the consumer on a real tiny Git snapshot, never a real role."""
    import gzip
    with tempfile.TemporaryDirectory(prefix='tests-used-gzip-binding-') as directory:
        root = Path(directory)
        path = 'tests/__gzip_binding__.log.gz'
        text = b'synthetic historical diagnostic: unverified\n'
        (root / 'tests').mkdir()
        (root / path).write_bytes(gzip.compress(text, mtime=0))
        v1.git(root, 'init', '-q')
        v1.git(root, 'add', '--', path)
        v1.git(root, '-c', 'user.name=control', '-c', 'user.email=control@example.invalid',
               'commit', '-qm', 'Synthetic gzip binding control')
        ref = v1.decode(v1.git(root, 'rev-parse', 'HEAD')).strip()
        blob = v1.decode(v1.git(root, 'rev-parse', 'HEAD:' + path)).strip()
        row = dict(path=path, blob=blob, decoded_sha256=v2.hashlib.sha256(text).hexdigest(),
                   anchor=text.decode().strip(), role='Synthetic diagnostic; no actual review credit.',
                   review=dict(content=text.decode(), producer='Synthetic control bytes.',
                               consumers='Synthetic input-selection control; no real-object claim.',
                               input_revision=ref, independent=True))
        data = dict(schema_version=2, records=[row])
        saved = globals()['catalog_document']
        try:
            globals()['catalog_document'] = lambda: {}
            baseline = current_inventory(root, ref, None)
            assert baseline['records'][0]['class'] is None
            globals()['catalog_document'] = lambda: {GZIP_KEY: data}
            selected = current_inventory(root, ref, None)
            assert selected['records'][0]['class'] == 'evidence'
            assert selected['records'][0]['recovery'] == baseline['records'][0]['recovery']
            assert selected['records'][0]['secondary']['historical_gzip_role'] == row
            explicit = root / 'explicit-empty.json'
            explicit.write_text(json.dumps(dict(schema_version=2, records=[])))
            # Existing explicit selection overrides embedded opt-in data.
            assert current_inventory(root, ref, explicit) == baseline
            explicit.write_text('null')
            for document, supplied in [({GZIP_KEY: data}, explicit), ({GZIP_KEY: None}, None)]:
                globals()['catalog_document'] = lambda: document
                try:
                    current_inventory(root, ref, supplied)
                except ValueError as error:
                    assert 'invalid gzip role catalog' in str(error)
                else:
                    raise AssertionError('present null role input silently disabled validation')
            globals()['catalog_document'] = lambda: {GZIP_KEY: data}
            row['review']['input_revision'] = 'f' * 40
            try:
                current_inventory(root, ref, None)
            except ValueError as error:
                assert 'stale gzip consumer-context review' in str(error)
            else:
                raise AssertionError('embedded catalog bypassed landed revision guard')
        finally:
            globals()['catalog_document'] = saved
    print('PASS H871 catalog binding: absent opt-in, exact object/recovery, explicit selection, null-input rejection and stale-context refusal')


def role_delta_controls():
    """Exercise actual CLI/private inputs on a disposable synthetic repository."""
    import subprocess
    with tempfile.TemporaryDirectory(prefix='tests-used-role-delta-') as directory:
        temporary = Path(directory)
        root, code = temporary / 'repo', temporary / 'code'
        root.mkdir()
        code.mkdir()
        (root / 'tests').mkdir()
        path = 'tests/role-control.txt'
        (root / path).write_text('synthetic unverified historical note\n')
        (root / 'context.py').write_text('REFERENCE = "tests/role-control.txt"\n')
        v1.git(root, 'init', '-q')
        v1.git(root, 'add', '.')
        v1.git(root, '-c', 'user.name=control', '-c', 'user.email=control@example.invalid',
               'commit', '-qm', 'Synthetic role-delta input')
        repo = v1.Repository(root, 'HEAD')
        catalog = dict(schema_version=3, standalone=[], module_entries=[], reads=[], generators=[], orphans=[])
        base = dict(schema_version=1, records=[])
        raw_catalog = canonical_private_json(catalog)
        document = encode(raw_catalog, catalog)
        for source in HERE.glob('check-tests-used*.py'):
            (code / source.name).write_bytes(source.read_bytes())
        (code / 'check-tests-used-routes.json').write_bytes(raw_catalog)
        (code / 'check-tests-used-roles.json').write_bytes(canonical_private_json(base))
        (code / 'check-tests-used-fixtures.json').write_bytes(canonical_private_json(dict(schema_version=2, records=[])))
        target = temporary / 'inventory.json'
        manifest_path, delta_path = temporary / 'manifest.json', temporary / 'delta.json'
        row = dict(path=path, blob=repo.tree[path][2], anchor='synthetic unverified historical note',
                   role='Historical record: Synthetic unverified diagnostic; no real-object approval.')
        delta = dict(schema_version=1, records=[row])
        locator = dict(repository='SolidiKeY/solidity-lean-coord', evidence_commit='a' * 40,
                       evidence_path='evidence/synthetic/delta.json')
        def pin(data=delta, change_manifest=None, delta_raw=None):
            raw = canonical_private_json(data) if delta_raw is None else delta_raw
            delta_path.write_bytes(raw)
            manifest = dict(locator, schema_version=1, input_revision=repo.ref,
                            base_sha256=v2.hashlib.sha256(canonical_private_json(base)).hexdigest(),
                            bytes=len(raw), sha256=v2.hashlib.sha256(raw).hexdigest())
            if change_manifest is not None:
                change_manifest(manifest)
            raw = canonical_private_json(manifest)
            manifest_path.write_bytes(raw)
            document[ROLE_DELTA_KEY] = dict(locator, bytes=len(raw), sha256=v2.hashlib.sha256(raw).hexdigest())
            save_document()
        def save_document():
            (code / 'check-tests-used-catalog-templates.json').write_bytes(canonical_private_json(document))
        def cli(*extra, status=1):
            result = subprocess.run([sys.executable, '-B', str(code / 'check-tests-used-catalog-templates.py'),
                     '--ref', repo.ref, '--export', '--artifact', str(target), *extra], cwd=root, capture_output=True)
            assert result.returncode == status, (result.stdout, result.stderr)
            return result
        flags = ['--historical-role-delta-manifest', str(manifest_path), '--historical-role-delta', str(delta_path)]
        save_document()
        baseline = v1.inventory(repo, catalog)
        cli()  # Full CLI no-opt-in output equals the unchanged frozen pipeline.
        assert target.read_bytes() == v1.output_json(baseline)
        pin()
        cli(*flags, status=0)
        candidate = parse(target.read_bytes())
        eligible = v1.reviewed_historical_notes(repo, delta)
        assert guard_role_delta(catalog, baseline, candidate, {path}, eligible) == candidate
        assert candidate['records'][0]['class'] == 'evidence'
        v1.verify(candidate, candidate)
        frozen_output = target.read_bytes()
        def must_refuse(extra=flags):
            result = cli(*extra)
            assert b'tests-used-templates:' in result.stderr
            assert target.read_bytes() == frozen_output  # Refusal never replaces output.
        for extra in [[], flags[:2], flags[2:]]:
            if extra:
                cli(*extra, status=2)
                assert target.read_bytes() == frozen_output
            else:
                must_refuse(extra)
        delta_path.write_bytes(delta_path.read_bytes() + b' ')
        must_refuse()
        pin()
        manifest_path.write_bytes(manifest_path.read_bytes() + b' ')
        must_refuse()
        for field, value in [('input_revision', 'b' * 40), ('base_sha256', '0' * 64),
                             ('schema_version', True), ('bytes', True), ('extra', 0),
                             ('bytes', MAX_ARTIFACT_BYTES + 1), ('repository', 'other/repo')]:
            pin(change_manifest=lambda data: data.update({field: value}))
            must_refuse()
        for invalid in [dict(delta, extra=0), dict(delta, schema_version=True),
                        dict(delta, records=[row, row]),
                        dict(delta, records=[dict(row, anchor='missing literal anchor')])]:
            pin(invalid)
            must_refuse()
        for raw in [b'{"schema_version":1,"schema_version":1,"records":[]}',
                    b'{"schema_version":1,"records":[],"x":NaN}', b'{}\n ']:
            pin(delta_raw=raw)
            must_refuse()
        pin(dict(delta, records=[dict(row, blob='0' * 40)]))
        cli(*flags)  # Stale object skips its role, exports unresolved baseline, exits 1.
        assert target.read_bytes() == v1.output_json(baseline)
        frozen_output = target.read_bytes()
        base['records'] = [row]
        (code / 'check-tests-used-roles.json').write_bytes(canonical_private_json(base))
        pin()
        must_refuse()  # Base/delta overlap is invalid even when definitions agree.
        base['records'] = []
        (code / 'check-tests-used-roles.json').write_bytes(canonical_private_json(base))
        pin()
        cli(*flags, status=0)
        frozen_output = target.read_bytes()
        refusal = dict(path=path, blob=row['blob'], reason='Synthetic exact regression fixture',
                       consumers=[dict(path='context.py', blob=repo.tree['context.py'][2],
                                       anchors=['REFERENCE = "tests/role-control.txt"'])])
        (code / 'check-tests-used-fixtures.json').write_bytes(
            canonical_private_json(dict(schema_version=2, records=[refusal])))
        must_refuse()  # The role cannot discard a newly exposed fixture-refusal blocker.
        (code / 'check-tests-used-fixtures.json').write_bytes(
            canonical_private_json(dict(schema_version=2, records=[])))
        for mutate in [lambda d: d.update(extra_header=0),
                       lambda d: d['records'][0].update(extra_row=0),
                       lambda d: d['records'][0].update(recovery=None),
                       lambda d: d['records'][0]['secondary'].update(extra_provenance=0)]:
            invalid = copy.deepcopy(candidate)
            mutate(invalid)
            try:
                guard_role_delta(catalog, baseline, invalid, {path}, eligible)
            except ValueError:
                pass
            else:
                raise AssertionError('role-delta accepted an added field or changed provenance')
        for marker in ['UNSUPPORTED_ORPHAN_REVIEW: synthetic', 'UNRESOLVED_READ_ROLE: synthetic',
                       'UNRESOLVED_GENERATED_CONSUMPTION: synthetic', 'UNVERIFIABLE: synthetic',
                       'FUTURE_UNKNOWN_BLOCKER: synthetic']:
            blocked = copy.deepcopy(baseline)
            blocked['records'][0]['unresolved'].append(marker)
            try:
                guard_role_delta(catalog, blocked, candidate, {path}, eligible)
            except ValueError:
                pass
            else:
                raise AssertionError('role-delta erased an independent blocker')
        for revision_pin in [repo.ref, 'f' * 40]:
            orphan = dict(path=path, input_revision=revision_pin, blob=row['blob'],
                          reason='Synthetic orphan review', dynamic_review='Candidate still present')
            blocked_catalog = dict(catalog, orphans=[orphan])
            if revision_pin == repo.ref:
                orphan_baseline = v1.inventory(repo, blocked_catalog)
                assert any(item.startswith('UNSUPPORTED_ORPHAN_REVIEW:')
                           for item in orphan_baseline['records'][0]['unresolved'])
                try:
                    guard_role_delta(catalog, orphan_baseline, candidate, {path}, eligible)
                except ValueError:
                    pass
                else:
                    raise AssertionError('post-flight failed the frozen-v1 orphan counterexample')
            document.update(encode(raw_catalog, blocked_catalog))
            save_document()
            must_refuse()  # Both current and inactive orphan records refuse the actual CLI.
        document.update(encode(raw_catalog, catalog))
        document.pop(ROLE_DELTA_KEY)
        save_document()
        must_refuse()  # Supplied files without the committed locator cannot opt in.
        cli()
        assert target.read_bytes() == v1.output_json(baseline)  # Invocation isolation.
    print('PASS role-delta controls: full CLI default equivalence, private bindings, orphan/blocker and exact-field refusals, stale skip versus anchor rejection, no real-role approval')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ref', default='origin/master')
    parser.add_argument('--artifact', type=Path, help='Private H145 inventory artifact, outside Git tracking')
    parser.add_argument('--roles', type=Path, help='Explicit independently reviewed H871 gzip roles')
    parser.add_argument('--historical-role-delta-manifest', type=Path)
    parser.add_argument('--historical-role-delta', type=Path)
    modes = parser.add_mutually_exclusive_group(required=True)
    for mode in ['write', 'check', 'self-test', 'export', 'check-manifest']:
        modes.add_argument('--' + mode, action='store_true')
    args = parser.parse_args()
    external = args.export or args.check_manifest
    if external != (args.artifact is not None) or args.roles is not None and not external:
        parser.error('--artifact is required only for --export/--check-manifest; --roles is exclusive to those modes')
    if ((args.historical_role_delta_manifest is None) != (args.historical_role_delta is None)
            or not external and args.historical_role_delta is not None):
        parser.error('historical role-delta files must be paired and require an external mode')
    try:
        if args.self_test:
            controls()
            manifest_controls()
            gzip_binding_controls()
            role_delta_controls()
            v2.controls()
            v1.self_test()
            return 0
        root = v1.decode(v1.git(Path.cwd(), 'rev-parse', '--show-toplevel')).strip()
        if external:
            manifest = catalog_document().get(MANIFEST_KEY)
            resolved = v1.decode(v1.git(root, 'rev-parse', '--verify', args.ref + '^{commit}')).strip()
            if args.check_manifest and (manifest is None or manifest['input_revision'] != resolved):
                raise ValueError('missing inventory manifest or mismatched resolved input revision')
            target = external_artifact(root, args.artifact)
            expected = current_inventory(root, resolved, args.roles,
                                         args.historical_role_delta_manifest, args.historical_role_delta)
            if args.export:
                raw = v1.output_json(expected)
                if len(raw) > MAX_ARTIFACT_BYTES:
                    raise ValueError('inventory exceeds private-evidence per-file limit')
                write_artifact(root, target, raw)
                print(json.dumps({'input_revision': resolved, 'bytes': len(raw),
                                  'sha256': v2.hashlib.sha256(raw).hexdigest()}, sort_keys=True))
            else:
                verify_manifest_artifact(root, manifest, expected, target)
        else:
            expected = v1.inventory(v1.Repository(root, args.ref), load_catalog())
            target = Path(root) / v1.OUTPUT
            if args.write:
                target.write_bytes(v1.output_json(expected))
            else:
                actual = parse(target.read_bytes())
                v1.verify(actual, expected)
                if target.read_bytes() != v1.output_json(expected):
                    raise ValueError('noncanonical inventory bytes')
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
