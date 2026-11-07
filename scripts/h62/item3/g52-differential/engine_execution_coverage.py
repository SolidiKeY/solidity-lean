#!/usr/bin/env python3
"""Guarded regression: resumed Engine-X ranges must not count overlapping cases,
bind-only rows, input-unbound payload evidence, incomplete jobs or changed validators
as native payload matches.
This checks external-test artifacts; it proves no source/runtime theorem.
"""
import argparse
import gzip
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter
from functools import lru_cache
from types import MappingProxyType
from pathlib import Path

HISTORICAL_WRAPPER = '13c4280d23c06b52215ae915143f7b3e4f3fe06a'
WRAPPER = 'scripts/h62/item3/g52-differential/engine_payload_reference.mjs'
ARCHIVE = '5dd08fee0fb41bc2a59bc4ab1dc75b19723fc71fe6af2f855454d3283fba09b9'


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def exact_nat(value, field):
    if type(value) is int and value >= 0:
        return value
    if isinstance(value, str) and re.fullmatch(r"0|[1-9][0-9]*", value):
        return int(value)
    raise ValueError("noncanonical integer observation: " + field)


def external_bounds(command, source):
    guard = command.get('external_guard')
    require(isinstance(guard, dict), 'missing external resource guard')
    expected = dict(schema=1, aggregate_rss_limit_bytes=12*1024**3,
                    address_space_soft_bytes=12*1024**3, address_space_hard_bytes=12*1024**3,
                    available_reserve_bytes=4*1024**3, swap_total_bytes=0,
                    sampling_interval_seconds=0.5, termination_grace_seconds=10,
                    process_group=True, rlimit_as_applied=True, lean_num_threads='1')
    require(all(type(guard.get(k)) is type(v) and guard[k] == v for k, v in expected.items()),
            'external resource guard settings')
    timeout = guard.get('timeout_seconds')
    require(type(timeout) is int and 0 < timeout <= 300 and
            guard.get('runner_sha256') == digest(source/'serial_semantics.py'),
            'external timeout/runner binding')
    require(type(command.get('seconds')) in (int, float) and 0 < command['seconds'] <= timeout+1 and
            type(command.get('peak_rss')) is int and 0 < command['peak_rss'] <= 12*1024**3 and
            type(guard.get('minimum_available_bytes')) is int and guard['minimum_available_bytes'] >= 4*1024**3,
            'external resource observations')


@lru_cache(maxsize=2)
def canonical_allocations(stream_name, index_name, stream_sha, index_sha):
    """Cache only immutable canonical metadata after verifying exact source bytes.
    Current file hashes are checked against regenerated archive expectations on
    every coverage call before this process-local cache can be consulted.
    All offset/record/source/member/genesis checks remain in this derivation.
    """
    require(digest(Path(stream_name)) == stream_sha and digest(Path(index_name)) == index_sha,
            'canonical allocation source changed')
    index = json.loads(Path(index_name).read_text())
    allocation_groups = {}
    offset = 0
    with Path(stream_name).open('rb') as stream:
        for raw in stream:
            decoded = json.loads(raw)
            key = Path(decoded['path']).stem
            entry = index.get(key)
            require(entry is not None and key not in allocation_groups and
                    entry['offset'] == offset and entry['length'] == len(raw) and
                    entry['record_sha256'] == hashlib.sha256(raw).hexdigest() and
                    entry['path'] == decoded['path'] and entry['source_sha256'] == decoded['source_sha256'],
                    'canonical allocation provenance mismatch')
            group = decoded['allocation']
            require(group['network'] == 'Osaka' and group['testCount'] == len(group['testIds']) and
                    len(set(group['testIds'])) == len(group['testIds']) and
                    group['preAccountCount'] == len(group['pre']), 'canonical allocation shape mismatch')
            allocation_groups[key] = dict(members=group['testIds'], genesis_hash=group['genesis']['hash'])
            offset += len(raw)
    require(len(allocation_groups) == len(index), 'canonical allocation group count mismatch')
    return json.dumps(allocation_groups, sort_keys=True)


@lru_cache(maxsize=2)
def canonical_payloads(input_name, index_name, stream_name, inventory_name,
                       input_sha, index_sha, stream_sha, inventory_sha, total):
    """Memoize immutable archive-bound expectations, never native outcomes.
    Every caller first hashes current input bytes against regenerated upstream
    expectations. Immutable tuples/proxies prevent callers altering cached data.
    """
    require(digest(Path(input_name)) == input_sha and digest(Path(index_name)) == index_sha and
            digest(Path(inventory_name)) == inventory_sha, 'canonical input source changed')
    index = json.loads(Path(index_name).read_text())
    allocation_groups = json.loads(canonical_allocations(stream_name, index_name, stream_sha, index_sha))
    for group in allocation_groups.values():
        group['members'] = set(group['members'])
    identities = []
    with gzip.open(inventory_name, 'rt') as stream:
        for line in stream:
            row = json.loads(line)
            if row.get('role') == 'fixture' and row.get('selection') == 'exact-osaka' and row.get('format') == 'blockchain_test_engine_x':
                identities.append((row['path'], row['case']))
    input_allocation_refs = []
    payload_expectations = []
    allowed_request_keys = {'forkchoiceUpdatedVersion', 'newPayloadVersion', 'params'}
    with gzip.open(input_name, 'rt') as stream:
        for i, line in enumerate(stream):
            record = json.loads(line)
            require(i < total and record['index'] == i and
                    (record['path'], record['case']) == identities[i] and
                    record['status'] == 'input-only-not-executed', 'input identity mismatch')
            fixture = record['fixture']
            require(fixture.get('network') == 'Osaka' and
                    fixture.get('_info', {}).get('fixture-format') == 'blockchain_test_engine_x',
                    'input format/fork mismatch')
            key = fixture.get('preHash')
            entry = index.get(key)
            require(entry is not None and record.get('allocation_ref') ==
                    dict(pre_hash=key, stream='engine-x-allocations.jsonl', **entry) and
                    record['case'] in allocation_groups[key]['members'], 'pinned input allocation mismatch')
            input_allocation_refs.append(record['allocation_ref'])
            requests = fixture.get('engineNewPayloads')
            require(isinstance(requests, list), 'input payload list missing')
            expected = []
            for request in requests:
                params = request.get('params') if isinstance(request, dict) else None
                if (not isinstance(request, dict) or set(request)-allowed_request_keys or
                    request.get('newPayloadVersion') not in (4, '4') or
                    request.get('forkchoiceUpdatedVersion') not in (3, '3') or
                    not isinstance(params, list) or len(params) != 4 or not isinstance(params[0], dict)):
                    expected = None
                    break
                payload = params[0]
                try:
                    hashes = [payload[key] for key in ('blockHash', 'parentHash', 'stateRoot')]
                    require(all(isinstance(v, str) and re.fullmatch('0x[0-9a-f]{64}', v) for v in hashes),
                            'invalid input payload hash')
                    require(isinstance(payload['transactions'], list), 'invalid input transaction list')
                    expected.append(dict(hash=payload['blockHash'], parent_hash=payload['parentHash'],
                                         state_root=payload['stateRoot'], number=int(payload['blockNumber'], 0),
                                         gas_used=int(payload['gasUsed'], 0), transactions=payload['transactions']))
                except (KeyError, TypeError, ValueError):
                    expected = None
                    break
            payload_expectations.append(expected)
    require(len(payload_expectations) == total, 'input payload expectation count mismatch')
    immutable_payloads = tuple(None if row is None else tuple(
        MappingProxyType({**payload, 'transactions': tuple(payload['transactions'])})
        for payload in row) for row in payload_expectations)
    return tuple(MappingProxyType(ref) for ref in input_allocation_refs), immutable_payloads, tuple(identities)


def coverage(repo, bulk, labels):
    require(labels and len(labels) == len(set(labels)), 'duplicate or empty run labels')
    require(all(re.fullmatch('[a-z0-9-]+', x) for x in labels), 'invalid run label')
    source = repo/'scripts/h62/item3/g52-differential'
    # Reject deficient current-run receipts before expensive archive work; the
    # original checks still run again at admission after archive verification.
    for label in labels:
        early = json.loads((bulk/('evidence/'+label+'-summary.json')).read_text())
        if early.get('adapter_sha256') == digest(repo/WRAPPER) and early.get('payload_execution_only') is True:
            command = json.loads((bulk/('evidence/'+label+'-command.json')).read_text())
            require('stopped' in command and command['stopped'] is None, 'stopped/incomplete native run')
            external_bounds(command, source)
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from eest_export import verify_engine_x_inputs
    archive_binding = verify_engine_x_inputs(bulk)
    read = lambda name: json.loads((bulk/name).read_text())
    export = read('evidence/engine-x-export.json')
    census = read('evidence/archive-census.json')
    require(export['archive_sha256'] == ARCHIVE, 'archive pin mismatch')
    require(export['census_sha256'] == digest(bulk/'evidence/archive-census.json'), 'census pin mismatch')
    require(export['stream_sha256'] == digest(bulk/'engine-x-inputs.jsonl.gz'), 'input pin mismatch')
    require(census['inventory_sha256'] == digest(bulk/'archive-inventory.jsonl.gz'), 'inventory pin mismatch')
    allocation = export['allocation']
    require(allocation['stream_sha256'] == digest(bulk/'engine-x-allocations.jsonl'), 'allocation stream mismatch')
    require(allocation['index_sha256'] == digest(bulk/'engine-x-allocations-index.json'), 'allocation index mismatch')
    index = read('engine-x-allocations-index.json')
    require(len(index) == allocation['groups'], 'allocation group count mismatch')
    identities = []
    with gzip.open(bulk/'archive-inventory.jsonl.gz', 'rt') as stream:
        for line in stream:
            row = json.loads(line)
            if row.get('role') == 'fixture' and row.get('selection') == 'exact-osaka' and row.get('format') == 'blockchain_test_engine_x':
                identities.append((row['path'], row['case']))
    total = export['cases']
    require(type(total) is int and total == archive_binding['cases'], 'archive case count mismatch')
    require(len(identities) == total, 'inventory count mismatch')
    # Expected execution commitments come from the independently pinned inputs,
    # never from two mutually agreeing lists supplied in a result artifact.
    # Re-derive canonical allocation membership/genesis from the pinned stream.
    # Looking up a result-supplied key in the index is not an input binding.
    allocation_groups = json.loads(canonical_allocations(
        str((bulk/'engine-x-allocations.jsonl').resolve()),
        str((bulk/'engine-x-allocations-index.json').resolve()),
        archive_binding['files']['engine-x-allocations.jsonl'],
        archive_binding['files']['engine-x-allocations-index.json']))
    for group in allocation_groups.values():
        group['members'] = set(group['members'])
    input_allocation_refs, payload_expectations, cached_identities = canonical_payloads(
        str((bulk/'engine-x-inputs.jsonl.gz').resolve()),
        str((bulk/'engine-x-allocations-index.json').resolve()),
        str((bulk/'engine-x-allocations.jsonl').resolve()),
        str((bulk/'archive-inventory.jsonl.gz').resolve()),
        archive_binding['files']['engine-x-inputs.jsonl.gz'],
        archive_binding['files']['engine-x-allocations-index.json'],
        archive_binding['files']['engine-x-allocations.jsonl'],
        archive_binding['files']['archive-inventory.jsonl.gz'], total)
    require(tuple(identities) == cached_identities, 'canonical input identities changed')
    source = repo/'scripts/h62/item3/g52-differential'
    wrapper_pins = {digest(repo/WRAPPER)}
    subprocess.run(['git', 'merge-base', '--is-ancestor', HISTORICAL_WRAPPER, 'HEAD'], cwd=repo, check=True, capture_output=True)
    old = subprocess.check_output(['git', 'show', HISTORICAL_WRAPPER+':'+WRAPPER], cwd=repo)
    wrapper_pins.add(hashlib.sha256(old).hexdigest())
    modules = {'native_worker_sha256': 'eest_reference.mjs', 'native_block_adapter_sha256': 'blockchain_adapter.mjs',
               'rejection_adapter_sha256': 'eest_rejection.mjs', 'resource_guard_sha256': 'host_resource_guard.mjs'}
    pins = {key: digest(source/name) for key, name in modules.items()}
    lock = digest(bulk/'reference/package-lock.json')
    require(lock == digest(repo/'tests/h62/item3/g52-differential/package-lock.json'), 'installed lock mismatch')
    visited = set()
    counts = Counter()
    transactions = logs = blocks = 0
    receipts = []
    for label in labels:
        summary = read('evidence/'+label+'-summary.json')
        command = read('evidence/'+label+'-command.json')
        rows_path = bulk/('evidence/'+label+'.jsonl')
        require(summary.get('original_format') == 'blockchain_test_engine_x' and summary.get('binding_only') is False and summary.get('payload_execution_only') is True, 'not a native Engine-X run: '+label)
        require(summary.get('adapter_sha256') in wrapper_pins, 'unbound wrapper version: '+label)
        require(summary.get('adapter_sha256') == digest(repo/WRAPPER), 'outdated wrapper version: '+label)
        require(all(summary.get(k) == v for k, v in pins.items()), 'changed validator: '+label)
        require(summary.get('reference_lock_sha256') == lock and summary.get('export_sha256') == digest(bulk/'evidence/engine-x-export.json') and summary.get('input_sha256') == export['stream_sha256'] and summary.get('inventory_sha256') == census['inventory_sha256'], 'run provenance mismatch: '+label)
        bound = summary['allocation_binding']
        require(bound['stream_sha256'] == allocation['stream_sha256'] and bound['index_sha256'] == allocation['index_sha256'] and bound['module_sha256'] == digest(source/'engine_x_allocation.mjs'), 'allocation binding version mismatch')
        require(summary.get('final_account_map_present') is False and summary.get('engine_rpc_complete') is False and summary.get('engine_fixture_conformance_complete') is False and summary.get('differential_complete') is False and summary.get('source_semantics_unsupported') == total, 'conflated conformance flags')
        require(type(summary['expected']) is int and type(summary['selected']) is int, 'noncanonical summary count')
        require(isinstance(summary['counts'], dict) and all(type(n) is int and n >= 0 for n in summary['counts'].values()), 'noncanonical status count')
        require(summary['expected'] == total and digest(rows_path) == summary['results_sha256'], 'row hash/count pin mismatch')
        cmd = command['command']
        require(7 <= len(cmd) <= 9 and cmd[:4] == ['node', '--max-old-space-size=4096', WRAPPER, str(bulk)] and cmd[5:7] == [label, 'blockchain_test_engine_x'], 'unbound native command')
        require(len(cmd) < 8 or cmd[7] == 'execute', 'non-execution command')
        start = summary.get('range_start', 0)
        end = summary.get('range_end', start+summary['selected'])
        requested_start = int(cmd[8]) if len(cmd) == 9 else 0
        require(type(start) is int and type(end) is int and 0 <= start < end <= total and start == requested_start and end == min(start+int(cmd[4]), total), 'incomplete/invalid requested range')
        require(summary['selected'] == end-start and 'stopped' in command and command['stopped'] is None, 'stopped/incomplete native run')
        external_bounds(command, source)
        require(type(summary.get('peak_aggregate_rss')) is int and 0 < summary['peak_aggregate_rss'] <= 12*1024**3, 'internal resource observation')
        raw_transactions = [tx for expected in payload_expectations[start:end] if expected
                            for payload in expected for tx in payload['transactions']]
        parsed = subprocess.run(['node', '--max-old-space-size=4096',
                                 str(source/'engine_input_transactions.mjs'), str(bulk)],
                                input=json.dumps(raw_transactions), text=True, capture_output=True,
                                cwd=repo, timeout=60, check=True)
        transaction_expectations = json.loads(parsed.stdout)
        require(isinstance(transaction_expectations, list) and len(transaction_expectations) == len(raw_transactions),
                'input transaction expectation count mismatch')
        transaction_position = 0
        expected_transactions = {}
        for input_index in range(start, end):
            expected = payload_expectations[input_index]
            if expected:
                by_block = []
                for payload in expected:
                    count = len(payload['transactions'])
                    by_block.append(transaction_expectations[transaction_position:transaction_position+count])
                    transaction_position += count
                expected_transactions[input_index] = by_block
        local = Counter()
        with rows_path.open() as stream:
            position = start
            for line in stream:
                row = json.loads(line)
                require(position < end and type(row['index']) is int and row['index'] == position and (row['path'], row['case']) == identities[position], 'range identity/count mismatch')
                require(position not in visited, 'overlapping native coverage: '+str(position))
                visited.add(position)
                position += 1
                status = row['status']
                require(status in {'payload_reference_match', 'payload_reference_mismatch', 'unsupported', 'engine_error'}, 'non-native result status')
                require(row.get('engine_rpc_complete') is False and row.get('forkchoice_executed') is False and row.get('source_semantics') == 'unsupported-adapter-pending', 'row source/RPC conflation')
                binding = row['allocation_binding']
                source_ref = input_allocation_refs[row['index']]
                require(binding['pre_hash'] == source_ref['pre_hash'], 'row allocation differs from pinned input')
                entry = index.get(source_ref['pre_hash'])
                require(entry is not None and binding['allocation_path'] == entry['path'] and binding['allocation_source_sha256'] == entry['source_sha256'] and binding['allocation_record_sha256'] == entry['record_sha256'] and binding['exact_case_membership'] is True and binding['environment_genesis_checked'] is True and binding['final_account_map_present'] is False, 'row allocation mismatch')
                local[status] += 1
                if status == 'payload_reference_match':
                    require(all(row.get(k) is True for k in ['header_validation', 'block_validation', 'block_size_validation']), 'match without native validators')
                    expected = payload_expectations[row['index']]
                    require(expected is not None and len(expected) > 0 and
                            isinstance(row.get('blocks'), list) and len(row['blocks']) == len(expected),
                            'payload block count differs from pinned input')
                    input_hashes = [x['hash'] for x in expected]
                    require(row['binding']['original_format'] == 'blockchain_test_engine_x' and
                            row['binding']['payload_block_hashes'] == input_hashes and
                            [x['hash'] for x in row['blocks']] == input_hashes and
                            row['binding']['genesis_hash'] == expected[0]['parent_hash'] == allocation_groups[source_ref['pre_hash']]['genesis_hash'] and
                            row['binding']['payload_versions'] == 4 and row['binding']['forkchoice_version'] == 3,
                            'payload block hashes differ from pinned input')
                    for block, source_payload, source_transactions in zip(row['blocks'], expected, expected_transactions[row['index']]):
                        require(block['state_root'] == source_payload['state_root'] and
                                exact_nat(block['number'], 'block number') == source_payload['number'] and
                                exact_nat(block['gas_used'], 'block gas') == source_payload['gas_used'],
                                'block header observation differs from pinned input')
                        require(isinstance(block['transactions'], list) and
                                len(block['transactions']) == len(source_payload['transactions']),
                                'transaction count differs from pinned input')
                        blocks += 1
                        cumulative = 0
                        for i, tx in enumerate(block['transactions']):
                            source_tx = source_transactions[i]
                            require(source_tx is not None and tx['hash'] == source_tx['hash'] and
                                    type(tx['type']) is int and tx['type'] == source_tx['type'] and exact_nat(tx['gas_limit'], 'gas limit') == exact_nat(source_tx['gas_limit'], 'input gas limit'),
                                    'transaction identity differs from pinned input')
                            require(type(tx['index']) is int and type(tx['receipt_status']) is int and tx['index'] == i and tx['receipt_status'] == (0 if tx['execution_exception'] else 1), 'transaction identity/status mismatch')
                            spent = exact_nat(tx['total_gas_spent'], 'gas spent')
                            require(0 <= spent <= exact_nat(source_tx['gas_limit'], 'input gas limit'), 'transaction gas outside pinned input limit')
                            cumulative += spent
                            require(cumulative == exact_nat(tx['receipt_cumulative_gas_used'], 'cumulative gas') and re.fullmatch('0x(?:[0-9a-f]{2})*', tx['output']), 'output/gas observation mismatch')
                            for field in ['execution_gas_used', 'native_gas_refund_counter']:
                                exact_nat(tx[field], field)
                            require(tx['execution_exception'] is None or (isinstance(tx['execution_exception'], str) and bool(tx['execution_exception'])), 'malformed execution exception')
                            require(isinstance(tx['logs'], list) and all(isinstance(log, dict) and set(log) == {'address', 'topics', 'data'} and isinstance(log['address'], str) and re.fullmatch('0x[0-9a-f]{40}', log['address']) and isinstance(log['topics'], list) and all(isinstance(topic, str) and re.fullmatch('0x[0-9a-f]{64}', topic) for topic in log['topics']) and isinstance(log['data'], str) and re.fullmatch('0x(?:[0-9a-f]{2})*', log['data']) for log in tx['logs']), 'malformed native logs')
                            require(not tx['execution_exception'] or not tx['logs'], 'failed transaction retained logs')
                            transactions += 1
                            logs += len(tx['logs'])
                        require(cumulative == exact_nat(block['gas_used'], 'block gas'), 'block gas mismatch')
            require(position == end, 'truncated native range')
        require(dict(local) == summary['counts'], 'status accounting mismatch')
        require(type(command['exit']) is int and command['exit'] == (1 if local['payload_reference_mismatch'] or local['engine_error'] else 2), 'wrong native exit')
        counts.update(local)
        receipts.append(dict(label=label, start=start, end=end, results_sha256=summary['results_sha256']))
    gaps = []
    start = None
    for i in range(total+1):
        missing = i < total and i not in visited
        if missing and start is None:
            start = i
        elif not missing and start is not None:
            gaps.append([start, i]); start = None
    return dict(expected=total, processed_unique_cases=len(visited), counts=dict(counts),
                unprocessed_cases=total-len(visited), unprocessed_ranges=gaps, runs=receipts,
                validated_blocks=blocks, transaction_observations=transactions, raw_log_entries=logs,
                final_account_map_present=False, engine_rpc_complete=False, differential_complete=False,
                source_matches=0, full_payload_match=counts['payload_reference_match'] == total,
                validator_sha256=pins, input_stream_sha256=export['stream_sha256'],
                input_payloads_bound=True, input_allocations_bound=True, input_transaction_identities_bound=True,
                input_transaction_parser_sha256=digest(source/'engine_input_transactions.mjs'),
                checker_sha256=digest(Path(__file__)), archive_binding=archive_binding)


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--bulk', type=Path, required=True)
    parser.add_argument('--labels', nargs='+', required=True)
    args = parser.parse_args()
    result = coverage(args.repo.resolve(), args.bulk.resolve(), args.labels)
    print(json.dumps(result, indent=2))
    return 1 if result['counts'].get('payload_reference_mismatch') or result['counts'].get('engine_error') else 2


if __name__ == '__main__':
    raise SystemExit(main())
