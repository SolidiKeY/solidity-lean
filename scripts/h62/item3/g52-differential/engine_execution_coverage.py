#!/usr/bin/env python3
"""Guarded regression: resumed Engine-X ranges must not count overlapping cases,
bind-only rows, incomplete jobs or changed validators as native payload matches.
This checks external-test artifacts; it proves no source/runtime theorem.
"""
import argparse
import gzip
import hashlib
import json
import re
import subprocess
from collections import Counter
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


def coverage(repo, bulk, labels):
    require(labels and len(labels) == len(set(labels)), 'duplicate or empty run labels')
    require(all(re.fullmatch('[a-z0-9-]+', x) for x in labels), 'invalid run label')
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
    require(len(identities) == total, 'inventory count mismatch')
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
        require(all(summary.get(k) == v for k, v in pins.items()), 'changed validator: '+label)
        require(summary.get('reference_lock_sha256') == lock and summary.get('export_sha256') == digest(bulk/'evidence/engine-x-export.json') and summary.get('input_sha256') == export['stream_sha256'] and summary.get('inventory_sha256') == census['inventory_sha256'], 'run provenance mismatch: '+label)
        bound = summary['allocation_binding']
        require(bound['stream_sha256'] == allocation['stream_sha256'] and bound['index_sha256'] == allocation['index_sha256'] and bound['module_sha256'] == digest(source/'engine_x_allocation.mjs'), 'allocation binding version mismatch')
        require(summary.get('final_account_map_present') is False and summary.get('engine_rpc_complete') is False and summary.get('engine_fixture_conformance_complete') is False and summary.get('differential_complete') is False and summary.get('source_semantics_unsupported') == total, 'conflated conformance flags')
        require(summary['expected'] == total and digest(rows_path) == summary['results_sha256'], 'row hash/count pin mismatch')
        cmd = command['command']
        require(7 <= len(cmd) <= 9 and cmd[:4] == ['node', '--max-old-space-size=4096', WRAPPER, str(bulk)] and cmd[5:7] == [label, 'blockchain_test_engine_x'], 'unbound native command')
        require(len(cmd) < 8 or cmd[7] == 'execute', 'non-execution command')
        start = summary.get('range_start', 0)
        end = summary.get('range_end', start+summary['selected'])
        requested_start = int(cmd[8]) if len(cmd) == 9 else 0
        require(type(start) is int and type(end) is int and 0 <= start < end <= total and start == requested_start and end == min(start+int(cmd[4]), total), 'incomplete/invalid requested range')
        require(summary['selected'] == end-start and 'stopped' in command and command['stopped'] is None, 'stopped/incomplete native run')
        local = Counter()
        with rows_path.open() as stream:
            position = start
            for line in stream:
                row = json.loads(line)
                require(position < end and row['index'] == position and (row['path'], row['case']) == identities[position], 'range identity/count mismatch')
                require(position not in visited, 'overlapping native coverage: '+str(position))
                visited.add(position)
                position += 1
                status = row['status']
                require(status in {'payload_reference_match', 'payload_reference_mismatch', 'unsupported', 'engine_error'}, 'non-native result status')
                require(row.get('engine_rpc_complete') is False and row.get('forkchoice_executed') is False and row.get('source_semantics') == 'unsupported-adapter-pending', 'row source/RPC conflation')
                binding = row['allocation_binding']
                entry = index.get(binding['pre_hash'])
                require(entry is not None and binding['allocation_path'] == entry['path'] and binding['allocation_source_sha256'] == entry['source_sha256'] and binding['allocation_record_sha256'] == entry['record_sha256'] and binding['exact_case_membership'] is True and binding['environment_genesis_checked'] is True and binding['final_account_map_present'] is False, 'row allocation mismatch')
                local[status] += 1
                if status == 'payload_reference_match':
                    require(all(row.get(k) is True for k in ['header_validation', 'block_validation', 'block_size_validation']), 'match without native validators')
                    require(row['binding']['original_format'] == 'blockchain_test_engine_x' and row['binding']['payload_block_hashes'] == [x['hash'] for x in row['blocks']], 'payload/executed block mismatch')
                    for block in row['blocks']:
                        blocks += 1
                        cumulative = 0
                        for i, tx in enumerate(block['transactions']):
                            require(tx['index'] == i and tx['receipt_status'] == (0 if tx['execution_exception'] else 1), 'transaction identity/status mismatch')
                            cumulative += int(tx['total_gas_spent'])
                            require(cumulative == int(tx['receipt_cumulative_gas_used']) and re.fullmatch('0x(?:[0-9a-f]{2})*', tx['output']), 'output/gas observation mismatch')
                            require(not tx['execution_exception'] or not tx['logs'], 'failed transaction retained logs')
                            transactions += 1
                            logs += len(tx['logs'])
                        require(cumulative == int(block['gas_used']), 'block gas mismatch')
            require(position == end, 'truncated native range')
        require(dict(local) == summary['counts'], 'status accounting mismatch')
        require(command['exit'] == (1 if local['payload_reference_mismatch'] or local['engine_error'] else 2), 'wrong native exit')
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
                validator_sha256=pins, checker_sha256=digest(Path(__file__)))


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
