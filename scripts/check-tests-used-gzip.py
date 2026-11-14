#!/usr/bin/env python3
"""Opt-in bounded gzip inspection for H871; no inventory promotion yet.

Frozen classifiers and their observation interfaces remain unchanged. This
module adds an exact-object adapter only when explicitly invoked.
Decoded content is historical text, never execution or deletion evidence.

Proposed H896 consumer contract (separate review required before adoption):
reviewed_objects(repo, catalog) validates schema_version=2
and records with exactly path, blob, decoded_sha256, anchor, role, review.
review has exactly content, producer, consumers, input_revision, independent.
The first three are nonempty written attestations for this individual object;
input_revision pins the reviewed consumer context to repo.ref, and independent
must be the JSON boolean true. These declarations do not authenticate review. A catalog is trusted review input, not a role
approval request. Before supplying it, the independent factory review must
affirmatively inspect that object's decoded content and producer/consumer
context. Nonempty strings, suffixes, scans and absent reader metadata do not
establish that review or nonuse. This module contains no real-object approvals.

apply_roles consumes only the unmodified fixture-refusal inventory rebuilt for
the same Repository snapshot; it returns a deep copy. It preserves live keep,
uncertain readers, fixture refusals and every other unresolved blocker. Callers
must retain frozen verify(..., require_complete=True) on rebuilt output; no
adapter result is execution, child/read/proof, deletion or census completion
credit. Recovery pins retain the frozen classifier's authored-change criteria.
The CLI is opt-in via --roles; --self-test uses only synthetic objects. It never
runs captured commands. Downstream consumers must not treat review prose as
an independently verified consumer graph or bypass the factory review.
"""
import hashlib
import zlib

# Separate bounds cover compressed input and expansion. Neither is a gate or
# execution budget; no extraction, filesystem access or subprocess is performed.
MAX_COMPRESSED = 1_000_000
MAX_DECODED = 1_000_000


def decode_member(raw):
    """Accept exactly one complete gzip member containing bounded UTF-8 text."""
    if not isinstance(raw, bytes) or len(raw) > MAX_COMPRESSED:
        raise ValueError('compressed input type or size')
    decoder = zlib.decompressobj(16 + zlib.MAX_WBITS)
    try:
        decoded = decoder.decompress(raw, MAX_DECODED + 1)
    except zlib.error as error:
        raise ValueError('invalid gzip member') from error
    if (len(decoded) > MAX_DECODED or not decoder.eof
            or decoder.unused_data or decoder.unconsumed_tail):
        raise ValueError('oversized, incomplete or multiple gzip members')
    try:
        text = decoded.decode('utf-8', errors='strict')
    except UnicodeDecodeError as error:
        raise ValueError('gzip text is not UTF-8') from error
    if '\0' in text:
        raise ValueError('gzip text contains NUL')
    return decoded, text


def anchored_text(raw, digest, anchor):
    """Check a decompressed SHA256 and a nonempty exact complete line.

    This does not establish the compressed Git object, current consumers,
    classification, recovery, or an independent object's review.
    """
    if (not isinstance(digest, str) or len(digest) != 64
            or any(c not in '0123456789abcdef' for c in digest)
            or not isinstance(anchor, str) or not anchor.strip()
            or any(c in anchor for c in '\r\n\0')):
        raise ValueError('invalid decoded digest or full-line anchor')
    decoded, text = decode_member(raw)
    if hashlib.sha256(decoded).hexdigest() != digest or anchor not in text.splitlines():
        raise ValueError('decoded digest or full-line anchor mismatch')
    return text


def controls():
    """Pure in-process controls; no tracked files or execution observations."""
    import gzip
    content = b'historical result: unverified\nsecond line\n'
    raw = gzip.compress(content, mtime=0)
    digest = hashlib.sha256(content).hexdigest()
    assert anchored_text(raw, digest, 'historical result: unverified') == content.decode()
    assert decode_member(gzip.compress(b'', mtime=0)) == (b'', '')
    invalid = [b'', b'not gzip', raw[:-1], raw + b'x', raw + raw,
               gzip.compress(b'\xff', mtime=0), gzip.compress(b'\0', mtime=0),
               gzip.compress(b'x' * (MAX_DECODED + 1), mtime=0),
               b'x' * (MAX_COMPRESSED + 1), bytearray(raw)]
    corrupt = bytearray(raw)
    corrupt[-8] ^= 1
    invalid.append(bytes(corrupt))
    for value in invalid:
        try:
            decode_member(value)
        except ValueError:
            pass
        else:
            raise AssertionError('unsafe gzip accepted')
    for bad_digest, bad_anchor in [(digest, 'historical result'), ('0' * 64, 'second line'),
                                   (digest.upper(), 'second line'), (digest, ''),
                                   (digest, 'second line\n'), (True, 'second line')]:
        try:
            anchored_text(raw, bad_digest, bad_anchor)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid digest/anchor accepted')
    assert len(decode_member(gzip.compress(b'x' * MAX_DECODED, mtime=0))[0]) == MAX_DECODED
    print('PASS H871 bounded gzip controls: single member, CRC, UTF-8, caps, exact digest/full line; no classification credit')


DEFAULT_UNRESOLVED = 'UNRESOLVED_USE: candidate search is not a certified use graph or proof of non-use'


def classifier():
    import importlib.util
    from pathlib import Path
    spec = importlib.util.spec_from_file_location('tests_used_gzip_fixtures',
            Path(__file__).with_name('check-tests-used-fixtures.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def reviewed_objects(repo, data):
    """Validate identity and explicit review fields; never infer a role by suffix."""
    if (not isinstance(data, dict) or set(data) != {'schema_version', 'records'}
            or type(data['schema_version']) is not int or data['schema_version'] != 2
            or not isinstance(data['records'], list)):
        raise ValueError('invalid gzip role catalog')
    seen, active = set(), []
    for row in data['records']:
        if (not isinstance(row, dict) or set(row) !=
                {'path', 'blob', 'decoded_sha256', 'anchor', 'role', 'review'}):
            raise ValueError('invalid gzip role record')
        path = row['path']
        if (not isinstance(path, str) or not path.startswith(('tests/', 'scripts/h55/', 'scripts/h62/'))
                or any(part in ('', '.', '..') for part in path.split('/'))
                or any(c in path for c in '\0\r\n') or path in seen
                or not isinstance(row['blob'], str) or len(row['blob']) != 40
                or any(c not in '0123456789abcdef' for c in row['blob'])
                or not isinstance(row['role'], str) or not row['role'].strip()
                or not isinstance(row['review'], dict)
                or set(row['review']) != {'content', 'producer', 'consumers', 'input_revision', 'independent'}
                or row['review']['independent'] is not True
                or any(not isinstance(row['review'][key], str) or not row['review'][key].strip()
                       for key in ('content', 'producer', 'consumers'))
                or not isinstance(row['review']['input_revision'], str)
                or len(row['review']['input_revision']) != 40
                or any(c not in '0123456789abcdef' for c in row['review']['input_revision'])):
            raise ValueError('unreviewed or duplicate gzip role')
        seen.add(path)
        # Validate the digest and anchor even when a historical object is absent.
        digest, anchor = row['decoded_sha256'], row['anchor']
        if (not isinstance(digest, str) or len(digest) != 64
                or any(c not in '0123456789abcdef' for c in digest)
                or not isinstance(anchor, str) or not anchor.strip()
                or any(c in anchor for c in '\r\n\0')):
            raise ValueError('invalid gzip role digest or anchor')
        if path not in repo.tree:
            continue
        if path not in repo.paths or repo.tree[path] != ('100644', 'blob', row['blob']):
            raise ValueError('stale or nonregular gzip role object: ' + path)
        if row['review']['input_revision'] != repo.ref:
            raise ValueError('stale gzip consumer-context review: ' + path)
        anchored_text(repo.bytes(path), digest, anchor)
        active.append(row)
    return active


def apply_roles(repo, original, data):
    """Apply individually reviewed historical roles, preserving every blocker.

    The review's consumer field must affirmatively address actual content and
    known producer/consumer context. Empty reader metadata is not nonuse proof.
    This adapter supplies no consumer, execution, proof or deletion authority.
    """
    import copy
    import shlex
    if not isinstance(original, dict) or original.get('measured_revision') != repo.ref:
        raise ValueError('gzip inventory differs from repository snapshot')
    roles = reviewed_objects(repo, data)
    output = copy.deepcopy(original)
    by_path = {row['path']: row for row in output['records']}
    for role in roles:
        row = by_path[role['path']]
        if (row['class'] is not None or row['unresolved'] != [DEFAULT_UNRESOLVED]
                or row['generator'] is not None or row['runner_chain'] is not None
                or row['orphan_analysis'] is not None
                or row['secondary'].get('unreviewed_readers')
                or 'reviewed_fixture_refusal' in row['secondary']):
            continue
        pin = row['recovery']
        if (not isinstance(pin, dict) or pin.get('blob') != role['blob']
                or not isinstance(pin.get('last_touch_commit'), str)
                or len(pin['last_touch_commit']) != 40
                or any(c not in '0123456789abcdef' for c in pin['last_touch_commit'])
                or pin.get('command') != 'git show ' + shlex.quote(pin['last_touch_commit'] + ':' + row['path'])):
            continue
        if (row['mode'], row['object_type'], row['blob']) != repo.tree[row['path']]:
            raise ValueError('gzip role differs from inventory object')
        row['class'] = 'evidence'
        row['reason'] = 'Historical gzip text with unverified claims: ' + role['role']
        row['secondary']['historical_gzip_role'] = copy.deepcopy(role)
        row['unresolved'] = []
    classes = ('keep', 'regenerable', 'evidence', 'orphan')
    output['totals'] = {**{c: sum(row['class'] == c for row in output['records']) for c in classes},
                        'paths': len(output['records']),
                        'unresolved': sum(bool(row['unresolved']) for row in output['records'])}
    return output


def adapter_controls():
    import copy
    import gzip
    import types
    raw = gzip.compress(b'old result: unverified\n', mtime=0)
    path, blob, commit = 'tests/history.log.gz', 'a' * 40, 'b' * 40
    role = dict(path=path, blob=blob, decoded_sha256=hashlib.sha256(b'old result: unverified\n').hexdigest(),
                anchor='old result: unverified', role='An old result log, not a live fixture.',
                review=dict(content='Full synthetic historical log reviewed.', producer='Synthetic old test report.',
                            consumers='Synthetic control has no consumer; no real-object nonuse conclusion.',
                            input_revision='c' * 40, independent=True))
    data = dict(schema_version=2, records=[role])
    repo = types.SimpleNamespace(ref='c' * 40, paths=[path],
                                 tree={path: ('100644', 'blob', blob)}, bytes=lambda p: raw)
    record = dict(path=path, **{'class': None}, reason='Unresolved', mode='100644', object_type='blob', blob=blob,
                  recovery=dict(last_touch_commit=commit, command='git show ' + commit + ':' + path, blob=blob),
                  runner_chain=None, secondary={}, search_candidates=[], generator=None, orphan_analysis=None,
                  unresolved=[DEFAULT_UNRESOLVED])
    original = dict(schema_version=4, measured_revision='c' * 40, analysis_gaps=[], records=[record],
                    totals=dict(paths=1, keep=0, regenerable=0, evidence=0, orphan=0, unresolved=1))
    before = copy.deepcopy(original)
    output = apply_roles(repo, original, data)
    assert original == before and output['records'][0]['class'] == 'evidence'
    expected = copy.deepcopy(before)
    expected['records'][0].update(**{'class': 'evidence'}, reason=output['records'][0]['reason'],
        secondary={'historical_gzip_role': role}, unresolved=[])
    expected['totals'].update(evidence=1, unresolved=0)
    assert output == expected and apply_roles(repo, output, data) == output
    for classification in ('keep', 'regenerable', 'evidence', 'orphan'):
        current = copy.deepcopy(original)
        current['records'][0]['class'] = classification
        current['records'][0]['unresolved'] = []
        current['totals'] = {**{c: int(c == classification) for c in ('keep', 'regenerable', 'evidence', 'orphan')},
                             'paths': 1, 'unresolved': 0}
        assert apply_roles(repo, current, data) == current
    for field, value in [('unresolved', [DEFAULT_UNRESOLVED, 'other blocker']), ('generator', {}),
            ('runner_chain', {}), ('orphan_analysis', {}), ('recovery', None),
            ('secondary', {'unreviewed_readers': ['real-reader']}),
            ('secondary', {'reviewed_fixture_refusal': {}})]:
        current = copy.deepcopy(original)
        current['records'][0][field] = value
        assert apply_roles(repo, current, data) == current
    absent = types.SimpleNamespace(paths=[], tree={})
    assert reviewed_objects(absent, data) == []
    mutations = []
    for key, value in [('schema_version', True), ('extra', 0), ('records', {})]:
        bad = copy.deepcopy(data)
        bad[key] = value
        mutations.append(bad)
    for key, value in [('path', 'tests/../history.log.gz'), ('path', 'outside/log.gz'), ('blob', 'd' * 40),
            ('decoded_sha256', '0' * 64), ('anchor', 'old result'), ('review', {}), ('role', '')]:
        bad = copy.deepcopy(data)
        bad['records'][0][key] = value
        mutations.append(bad)
    bad = copy.deepcopy(data)
    bad['records'] *= 2
    mutations.append(bad)
    for bad in mutations:
        try:
            apply_roles(repo, original, bad)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid gzip role accepted')
    # Review provenance is per object: missing, extra and blank review fields
    # fail even when the object is absent at this historical revision.
    for field in ('content', 'producer', 'consumers'):
        for value in ('', '   ', None, True, []):
            bad = copy.deepcopy(data)
            bad['records'][0]['review'][field] = value
            mutations.append(bad)
        bad = copy.deepcopy(data)
        del bad['records'][0]['review'][field]
        mutations.append(bad)
    for field, value in [('extra', 1), ('anchor', 'old result: unverified\n'),
                         ('decoded_sha256', True), ('blob', 'A' * 40)]:
        bad = copy.deepcopy(data)
        bad['records'][0][field] = value
        mutations.append(bad)
    bad = copy.deepcopy(data)
    bad['records'][0]['review']['extra'] = 'unrecognized attestation'
    mutations.append(bad)
    for bad in mutations:
        try:
            reviewed_objects(repo, bad)
        except ValueError:
            pass
        else:
            raise AssertionError('malformed per-object review accepted')
    for mode, kind in [('100755', 'blob'), ('120000', 'blob'), ('160000', 'commit')]:
        stale = types.SimpleNamespace(paths=[path], tree={path: (mode, kind, blob)}, bytes=repo.bytes)
        try:
            reviewed_objects(stale, data)
        except ValueError:
            pass
        else:
            raise AssertionError('nonregular tracked object accepted')
    for member in (raw + raw, raw[:-1], raw + b'x',
                   gzip.compress(b'x' * (MAX_DECODED + 1), mtime=0)):
        malformed = types.SimpleNamespace(paths=[path], tree=repo.tree, bytes=lambda p: member, ref=repo.ref)
        try:
            reviewed_objects(malformed, data)
        except ValueError:
            pass
        else:
            raise AssertionError('adapter bypassed bounded single-member decoder')
    for pin in (dict(blob='d' * 40, last_touch_commit=commit, command='git show ' + commit + ':' + path),
                dict(blob=blob, last_touch_commit='HEAD', command='git show HEAD:' + path),
                dict(blob=blob, last_touch_commit=commit, command='echo captured command')):
        current = copy.deepcopy(original)
        current['records'][0]['recovery'] = pin
        assert apply_roles(repo, current, data) == current
    for field, values in [('independent', [False, 1, 'true', None]),
                          ('input_revision', ['HEAD', 'd' * 40, True, 'C' * 40])]:
        for value in values:
            bad = copy.deepcopy(data)
            bad['records'][0]['review'][field] = value
            try:
                reviewed_objects(repo, bad)
            except ValueError:
                pass
            else:
                raise AssertionError('unaffirmed or stale review accepted')
        bad = copy.deepcopy(data)
        del bad['records'][0]['review'][field]
        try:
            reviewed_objects(repo, bad)
        except ValueError:
            pass
        else:
            raise AssertionError('missing review context accepted')
    stale = copy.deepcopy(original)
    stale['measured_revision'] = 'd' * 40
    try:
        apply_roles(repo, stale, data)
    except ValueError:
        pass
    else:
        raise AssertionError('stale input inventory accepted')
    # Mutating returned review metadata cannot mutate the catalog or input.
    output['records'][0]['secondary']['historical_gzip_role']['review']['content'] = 'changed'
    assert data['records'][0]['review']['content'] == role['review']['content']
    assert original == before
    fixtures = classifier()
    for raw_json in (b'{"schema_version":2,"schema_version":2,"records":[]}',
                     b'{"schema_version":2,"records":[],"records":[]}'):
        try:
            fixtures.templates.parse(raw_json)
        except ValueError:
            pass
        else:
            raise AssertionError('duplicate JSON keys accepted')
    original['schema_version'] = fixtures.v1.SCHEMA
    fixtures.v1.verify(original, original, require_complete=False)
    try:
        fixtures.v1.verify(original, original)
    except ValueError as error:
        assert 'incomplete classification: 1 unresolved paths' in str(error)
    else:
        raise AssertionError('unchanged completeness bypassed')
    print('PASS H871 adapter controls: exact object, reviews, stale/refusal/keep precedence, unchanged completeness')


def main():
    import argparse
    import json
    from pathlib import Path
    import sys
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ref', default='origin/master')
    parser.add_argument('--roles', type=Path, help='Explicit independently reviewed gzip role catalog')
    modes = parser.add_mutually_exclusive_group(required=True)
    for name in ('write', 'check', 'self-test'):
        modes.add_argument('--' + name, action='store_true')
    args = parser.parse_args()
    if args.self_test:
        controls()
        adapter_controls()
        return 0
    if args.roles is None:
        parser.error('--roles is required; gzip classification is opt-in')
    fixtures = classifier()
    v1 = fixtures.v1
    try:
        root = v1.decode(v1.git(Path.cwd(), 'rev-parse', '--show-toplevel')).strip()
        repo = v1.Repository(root, args.ref)
        original = fixtures.inventory(repo, fixtures.templates.load_catalog())
        expected = apply_roles(repo, original, fixtures.templates.parse(args.roles.read_bytes()))
        target = Path(root) / v1.OUTPUT
        if args.write:
            target.write_bytes(v1.output_json(expected))
        else:
            actual = fixtures.templates.parse(target.read_bytes())
            v1.verify(actual, expected)
            if target.read_bytes() != v1.output_json(expected):
                raise ValueError('noncanonical inventory bytes')
        print(json.dumps(expected['totals'], sort_keys=True))
        if expected['totals']['unresolved'] or expected['analysis_gaps']:
            print('INCOMPLETE: no pruning authorization.', file=sys.stderr)
            return 1
        return 0
    except (ValueError, OSError, KeyError, TypeError, AssertionError) as error:
        print('tests-used-gzip: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
