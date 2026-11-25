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


def descriptor_generations(events):
    live, ended, reads, positions, offsets = {}, {}, {}, {}, {}
    def close(key, sequence):
        generation = live.pop(key, None)
        offsets.pop(key, None)
        if generation is not None:
            ended[(key[0], key[1], generation)] = sequence
    for event in events:
        identity, sequence = event['identity'], event['sequence']
        if event['kind'] in ('exec', 'exiting', 'exit'):
            for key in list(live):
                if key[0] == identity:
                    close(key, sequence)
        if event['kind'] != 'leave' or event.get('result', -1) < 0 or 'number' not in event:
            continue
        number, args, result = event['number'], event['args'], event['result']
        if number in (0, 17, 19):
            key = (identity, args[0])
            reads[sequence] = live.get(key)
            if key in offsets:
                positions[sequence] = args[3] if number == 17 else offsets[key][0]
                if number != 17 and offsets[key][0] is not None:
                    offsets[key][0] += result
        if number in (2, 257, 437):
            key = (identity, result)
            require(key not in live, 'open reused live descriptor')
            live[key] = sequence
            offsets[key] = [0]
        if number == 8 and (identity, args[0]) in offsets:
            holder = offsets[(identity, args[0])]
            delta = args[1] if args[1] < 2**63 else args[1] - 2**64
            if args[2] == 0:
                require(result == delta, 'SEEK_SET result mismatch')
            elif args[2] == 1 and holder[0] is not None:
                require(result == holder[0] + delta, 'SEEK_CUR result mismatch')
            holder[0] = result
        if number in (40, 275, 326):
            source_fd = args[1] if number == 40 else args[0]
            key = (identity, source_fd)
            if key in offsets:
                offsets[key][0] = None  # kernel-copy offset semantics not supported here
        if number == 3:
            close((identity, args[0]), sequence)
        if number == 436:
            raise Invalid('unsupported close_range observation')
        if number in (32, 33, 292) or number == 72 and args[1] in (0, 1030):
            source, destination = (identity, args[0]), (identity, result)
            if source != destination:
                close(destination, sequence)
                if source in live:
                    live[destination] = sequence
                    offsets[destination] = offsets[source]
    return reads, ended, positions


def replay_capture(capture, events, *, max_capture_bytes, max_events):
    """Independently replay raw payload consistency, not authenticate collection.

    A replayed result carries no census credit. Host custody, producer source,
    actual source/context association and ordinary-run evidence are still needed.
    """
    import base64
    import binascii
    require(type(max_capture_bytes) is int and max_capture_bytes > 0, 'replay byte budget')
    require(type(max_events) is int and max_events > 0, 'replay event budget')
    require(type(capture) is dict and set(capture) == {'status', 'reasons', 'targets', 'records'}, 'capture keys')
    if capture['status'] != 'captured':
        return dict(status='unavailable', credit='none', reasons=['capture unavailable'])
    require(capture['reasons'] == [], 'captured with refusal reasons')
    require(type(events) is list and len(events) <= max_events, 'raw event extent')
    require(type(capture['records']) is list and len(capture['records']) <= max_events, 'raw record extent')
    require(type(capture['targets']) is dict and bool(capture['targets']), 'target pins')
    for index, event in enumerate(events):
        require(type(event) is dict and event.get('sequence') == index, 'event sequence gap')
        shape(event['sequence'], 'uint')
        shape(event.get('identity'), 'text')
        shape(event.get('tid'), 'positive')
        shape(event.get('kind'), 'text')
        if event['kind'] == 'leave':
            shape(event.get('result'), 'integer')
        if 'number' in event or 'args' in event:
            shape(event.get('number'), 'uint')
            require(type(event.get('args')) is list and len(event['args']) == 6, 'syscall arguments')
            for value in event['args']:
                shape(value, 'uint')
    generations, endings, positions = descriptor_generations(events)
    pins = capture['targets']
    for path, pin in pins.items():
        shape(path, 'text')
        require(type(pin) is dict and set(pin) == {'device', 'inode', 'bytes', 'sha256'}, 'target pin keys')
        for key in ('device', 'inode', 'bytes'):
            shape(pin[key], 'uint')
        shape(pin['sha256'], 'sha')
        require(pin['bytes'] <= max_capture_bytes, 'pinned target budget')
    groups, used = {}, 0
    fields = {'target', 'sequence', 'open_sequence', 'close_sequence', 'task', 'fd', 'fd_generation',
              'device', 'inode', 'offset', 'bytes', 'requested', 'data', 'sha256'}
    for record in capture['records']:
        require(type(record) is dict and set(record) == fields, 'raw read keys')
        for key in fields - {'target', 'task', 'data', 'sha256'}:
            shape(record[key], 'uint')
        for key in ('target', 'task'):
            shape(record[key], 'text')
        shape(record['sha256'], 'sha')
        require(record['target'] in pins, 'unbound captured target')
        pin = pins[record['target']]
        require((record['device'], record['inode']) == (pin['device'], pin['inode']), 'target inode mismatch')
        start, number, end = record['open_sequence'], record['sequence'], record['close_sequence']
        require(start < number < end < len(events), 'captured descriptor lifetime')
        opened, read, closed = events[start], events[number], events[end]
        require(all(x.get('identity') == record['task'] for x in (opened, read, closed)), 'process lifetime mismatch')
        require(opened.get('kind') == 'leave' and opened.get('result') == record['fd']
                and opened.get('number') in (2, 257, 437, 32, 33, 72, 292), 'descriptor origin mismatch')
        require(record['fd_generation'] == start and generations.get(number) == start, 'descriptor generation mismatch')
        require(positions.get(number) == record['offset'], 'descriptor offset mismatch')
        require(endings.get((record['task'], record['fd'], start)) == end, 'intervening descriptor close/rebind')
        require(closed.get('kind') in ('exiting', 'exit') or
                closed.get('kind') == 'leave' and closed.get('number') == 3
                and closed.get('args', [None])[0] == record['fd'] and closed.get('result') == 0,
                'descriptor end mismatch')
        require(read.get('kind') == 'leave' and read.get('number') in (0, 17, 19)
                and read.get('result') == record['bytes'], 'actual read mismatch')
        args = read.get('args')
        require(type(args) is list and len(args) == 6 and args[0] == record['fd'], 'read descriptor mismatch')
        entry_number = read.get('enter_sequence')
        shape(entry_number, 'uint')
        require(start < entry_number < number, 'syscall entry order')
        entry = events[entry_number]
        require(entry.get('kind') == 'enter' and entry.get('identity') == record['task']
                and entry.get('number') == read['number'] and entry.get('args') == args, 'entry/return mismatch')
        if read['number'] == 19:
            vectors = entry.get('entry_iovecs')
            require(type(vectors) is list and len(vectors) == args[2] <= 1024, 'entry iovec snapshot')
            for vector in vectors:
                require(type(vector) in (list, tuple) and len(vector) == 2, 'iovec pair')
                for item in vector:
                    shape(item, 'uint')
            ranges = sorted((a, a + n) for a, n in vectors if n)
            require(all(b < 2**64 for _, b in ranges)
                    and all(a[1] <= b[0] for a, b in zip(ranges, ranges[1:])), 'unsafe iovec ranges')
            requested = sum(n for _, n in vectors)
        else:
            requested = args[2]
        require(requested == record['requested'] and requested > 0 and record['bytes'] <= requested, 'read request mismatch')
        if read['number'] == 17:
            require(record['offset'] == args[3], 'pread offset mismatch')
        require(record['offset'] + record['bytes'] <= pin['bytes'], 'captured byte range')
        used += record['bytes']
        require(used <= max_capture_bytes, 'raw payload budget')
        encoded = record['data']
        require(type(encoded) is str and len(encoded) == 4 * ((record['bytes'] + 2) // 3), 'encoded payload extent')
        try:
            payload = base64.b64decode(encoded, validate=True)
        except (ValueError, binascii.Error) as error:
            raise Invalid('invalid raw byte payload') from error
        require(len(payload) == record['bytes'] and hashlib.sha256(payload).hexdigest() == record['sha256'], 'returned payload digest')
        groups.setdefault((record['target'], record['task'], record['fd'], start), []).append((record, payload))
    complete = {}
    for (path, _, _, _), chunks in groups.items():
        pin = pins[path]
        chunks = [(r, data) for r, data in chunks if data or pin['bytes'] == 0]
        chunks.sort(key=lambda x: x[0]['offset'])
        if pin['bytes'] == 0:
            chunks = chunks[:1]
        offset, digest, intervals = 0, hashlib.sha256(), []
        for record, payload in chunks:
            if record['offset'] != offset:
                break
            offset += len(payload)
            digest.update(payload)
            intervals.append(dict(offset=record['offset'], bytes=len(payload),
                                  returned_bytes_sha256=record['sha256'], event_sequence=record['sequence']))
        else:
            if intervals and offset == pin['bytes']:
                require(digest.hexdigest() == pin['sha256'], 'full target payload mismatch')
                complete.setdefault(path, dict(path=path, bytes=offset, sha256=pin['sha256'], intervals=intervals))
    if set(complete) != set(pins):
        return dict(status='unavailable', credit='none', reasons=['no complete supported descriptor span'])
    return dict(status='replayed', credit='none', targets=[complete[p] for p in sorted(complete)])
