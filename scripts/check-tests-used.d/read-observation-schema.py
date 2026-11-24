"""Strict private observation metadata, not a consumer registry or a read certificate.

H1390 P1. Shape/consistency checks do not authenticate producer events. All byte
payloads, host provenance and context reviews still need independent verification.
No existing collector or checker calls this module by default.
"""
import hashlib
import json
import re

MAX_METADATA_BYTES = 204800


class Invalid(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Invalid(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def bounded_integer(text):
    require(len(text.lstrip('-')) <= 20, 'integer encoding too large')
    value = int(text)
    require(abs(value) < 2**64, 'integer encoding range')
    return value


def reject_float(_):
    raise Invalid('noninteger numeric metadata')


def decode(data):
    require(type(data) is bytes and len(data) <= MAX_METADATA_BYTES, 'metadata size/type')
    try:
        return json.loads(data.decode('utf-8'), object_pairs_hook=unique,
                          parse_int=bounded_integer, parse_float=reject_float, parse_constant=reject_float)
    except (UnicodeError, ValueError, RecursionError) as error:
        raise Invalid('invalid observation JSON') from error


# Compact type declarations mirror the private h145.* /1 drafts. A successful
# check below is metadata validity only, never approval of those draft schemas.
DEFINITIONS = {
    'artifact': dict(path='text', sha256='sha', bytes='uint'),
    'source': dict(path='text', blob='git', sha256='sha', bytes='uint', revision='git'),
    'frame': dict(source='source', line='positive', qualname='text', code_sha256='sha'),
    'tool': dict(path='text', sha256='sha', version='text'),
    'environment': dict(name='text', value='string'),
    'invocation': dict(argv=('text', 1), cwd='text', env=('environment', 0),
                       tools=('tool', 1), inputs=('source', 1), external_inputs=('artifact', 0),
                       external_outputs=('text', 0), timeout_seconds='positive'),
    'producer': dict(name='text', adapter='text', source='artifact', binary='?artifact',
                     kernel='text', runtime_tools=('tool', 1), config='artifact',
                     raw_events='artifact', trusted_host_statement='artifact'),
    'process': dict(run_nonce='sha', pid='positive', start_identity='text',
                    parent_start_identity='?text', exec_sequence='uint', executable='tool', argv=('text', 1)),
    'interval': dict(offset='uint', bytes='uint', returned_bytes_sha256='sha', event_sequence='uint'),
    'read': dict(target='source', namespace='text', process='process', fd_identity='text',
                 open_event_sequence='uint', close_event_sequence='uint', intervals=('interval', 1),
                 complete_target_sha256='sha', frames=('frame', 0), entered_branch_events=('artifact', 1),
                 mutation_audit='artifact', pre_identity='artifact', post_identity='artifact'),
    'outcome': dict(exit='?integer', signal='?positive', timed_out='bool', phase='text', log='artifact'),
    'observation': dict(invocation='invocation', producer='producer', reader='source', read='read',
                        outcome='outcome', ordinary_outcome='outcome', pre_manifest='artifact', post_manifest='artifact'),
    'cli_context': dict(reader='source', introducing_commit='git', reviewed_argv=('text', 1),
                        observed_revision='git', failure_frame='frame', failure_event_sequence='uint',
                        diagnostic_fingerprint_sha256='sha', read_event_sequences=('uint', 1),
                        normal_and_traced_context_equivalence_review='artifact', historical='bool',
                        current_blob_equivalence_review='artifact'),
}


def shape(value, kind, depth=0):
    require(depth < 64, 'metadata nesting')
    if isinstance(kind, tuple):
        item, minimum = kind
        require(type(value) is list and len(value) >= minimum, 'invalid list')
        for entry in value:
            shape(entry, item, depth + 1)
        return
    if kind.startswith('?'):
        if value is not None:
            shape(value, kind[1:], depth + 1)
        return
    if kind in DEFINITIONS:
        fields = DEFINITIONS[kind]
        require(type(value) is dict and set(value) == set(fields), 'invalid ' + kind + ' keys')
        for key, field_kind in fields.items():
            shape(value[key], field_kind, depth + 1)
    elif kind in ('integer', 'uint', 'positive'):
        require(type(value) is int and abs(value) < 2**64, 'integer type/range')
        require(kind == 'integer' or value >= (kind == 'positive'), 'integer bound')
    elif kind == 'bool':
        require(type(value) is bool, 'boolean type')
    else:
        require(type(value) is str and '\0' not in value, 'string type/content')
        if kind == 'text':
            require(bool(value), 'empty text')
        elif kind == 'sha':
            require(re.fullmatch('[0-9a-f]{64}', value) is not None, 'SHA256 identity')
        elif kind == 'git':
            require(re.fullmatch('(?:[0-9a-f]{40}|[0-9a-f]{64})', value) is not None, 'Git identity')
        else:
            require(kind == 'string', 'unknown metadata kind')


def distinct(values, key, label):
    keys = [key(value) for value in values]
    require(len(keys) == len(set(keys)), 'duplicate ' + label)


def outcome(value):
    require((value['exit'] is None) != (value['signal'] is None), 'ambiguous termination')
    require(value['exit'] is None or 0 <= value['exit'] <= 255, 'exit range')
    require(not value['timed_out'], 'timeout unavailable')


def validate_receipt(record):
    require(type(record) is dict, 'receipt object')
    kind = record.get('schema')
    require(kind in ('h145.exact-byte-read/1', 'h145.nonpassing-cli/1'), 'unknown draft schema')
    if record.get('availability') == 'unavailable':
        require(set(record) == {'schema', 'availability', 'missing', 'source_report'}, 'unavailable keys')
        shape(record['missing'], ('text', 1))
        shape(record['source_report'], 'artifact')
        return record
    require(record.get('availability') == 'available', 'unknown availability')
    keys = {'schema', 'availability', 'observation'}
    if kind == 'h145.nonpassing-cli/1':
        keys.add('context')
    require(set(record) == keys, 'available receipt keys')
    obs = record['observation']
    shape(obs, 'observation')
    producer = obs['producer']
    require(producer['name'] == 'h145-host-observed-byte-reader-v1', 'producer name')
    require(producer['adapter'] in ('python-audit-kernel', 'host-syscall-byte-capture'), 'adapter')
    invocation = obs['invocation']
    distinct(invocation['env'], lambda x: x['name'], 'environment name')
    distinct(invocation['inputs'], lambda x: x['path'], 'input path')
    distinct(invocation['external_inputs'], lambda x: x['path'], 'external input path')
    for result in (obs['outcome'], obs['ordinary_outcome']):
        outcome(result)
    require(all(obs['outcome'][key] == obs['ordinary_outcome'][key]
                for key in ('exit', 'signal', 'phase')), 'ordinary/instrumented outcome mismatch')
    read = obs['read']
    require(read['namespace'] in ('working-tree', 'git-object', 'external-mirror'), 'target namespace')
    require(read['complete_target_sha256'] == read['target']['sha256'], 'target digest mismatch')
    require(read['process']['argv'] == invocation['argv'], 'process argv mismatch')
    require(read['process']['executable'] == invocation['tools'][0], 'process executable mismatch')
    require(obs['reader'] in invocation['inputs'], 'reader absent from inputs')
    start, end = read['open_event_sequence'], read['close_event_sequence']
    require(start < end, 'open/close order')
    intervals = read['intervals']
    distinct(intervals, lambda x: x['event_sequence'], 'read event')
    offset = 0
    for interval in sorted(intervals, key=lambda x: x['offset']):
        require(start < interval['event_sequence'] < end, 'read outside descriptor lifetime')
        require(interval['offset'] == offset, 'gapped/overlapping byte ranges')
        require(interval['bytes'] > 0 or read['target']['bytes'] == 0, 'zero-byte no-op')
        offset += interval['bytes']
    require(offset == read['target']['bytes'], 'incomplete byte extent')
    if len(intervals) == 1:
        require(intervals[0]['returned_bytes_sha256'] == read['target']['sha256'], 'whole-range hash mismatch')
    if offset == 0:
        require(read['target']['sha256'] == hashlib.sha256(b'').hexdigest(), 'empty target digest')
        require(len(intervals) == 1 and intervals[0]['returned_bytes_sha256'] == hashlib.sha256(b'').hexdigest(),
                'empty target interval')
    if kind == 'h145.nonpassing-cli/1':
        context = record['context']
        shape(context, 'cli_context')
        require(context['reader'] == obs['reader'], 'CLI reader mismatch')
        require(context['reviewed_argv'] == invocation['argv'], 'CLI argv mismatch')
        require(context['observed_revision'] == obs['reader']['revision'], 'CLI revision mismatch')
        require(obs['outcome']['exit'] != 0, 'nonpassing CLI completed successfully')
        require(sorted(context['read_event_sequences']) == sorted(x['event_sequence'] for x in intervals),
                'CLI read events mismatch')
        require(all(x < context['failure_event_sequence'] for x in context['read_event_sequences']),
                'read after failure')
    return record
