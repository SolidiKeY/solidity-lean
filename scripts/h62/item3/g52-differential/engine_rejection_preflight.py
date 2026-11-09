#!/usr/bin/env python3
"""Guarded regression: mutable rejection receipts, weakened resource guards,
changed validators and source/positive-coverage conflation must fail preflight.
This is archive/identity/receipt preflight ONLY: native category, transaction,
conversion and full observation qualification remain separate unfinished work.
No output from this module admits coverage or establishes native/Source agreement.
Run CLI under the existing writer lock and external serial resource guard.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import re

from engine_execution_coverage import digest, require, external_bounds

RUNNER = 'scripts/h62/item3/g52-differential/engine_rejection_runner.mjs'
MODULES = ('engine_rejection_runner.mjs', 'engine_rejection_reference.mjs',
           'engine_payload_reference.mjs', 'engine_x_allocation.mjs',
           'eest_reference.mjs', 'eest_observation.mjs', 'blockchain_adapter.mjs',
           'eest_rejection.mjs', 'host_resource_guard.mjs', 'serial_semantics.py',
           'eest_export.py', 'archive_census.py', 'pipeline.py')
STATUSES = {'payload_rejection_reference_match', 'payload_rejection_mismatch',
            'engine_error', 'unsupported'}


def receipt_preflight(repo, bulk, label, summary, command, raw):
    require(isinstance(label, str) and re.fullmatch('[a-z0-9-]+', label), 'invalid rejection label')
    require(type(summary.get('schema')) is int and summary['schema'] == 1 and
            summary.get('original_format') == 'blockchain_test_engine_x', 'wrong rejection summary schema/format')
    indices = summary.get('indices')
    require(isinstance(indices, list) and 1 <= len(indices) <= 4 and
            all(type(n) is int and 0 <= n <= 2**53-1 for n in indices) and
            all(a < b for a, b in zip(indices, indices[1:])), 'noncanonical rejection selection')
    require(type(summary.get('selected')) is int and summary['selected'] == len(indices), 'rejection selected count')
    flags = ('coverage_admitted', 'engine_rpc_complete', 'forkchoice_executed',
             'differential_complete', 'full_conformance', 'final_account_map_present')
    require(all(summary.get(key) is False for key in flags) and
            type(summary.get('source_matches')) is int and summary['source_matches'] == 0,
            'conflated rejection/source/coverage flags')
    source = repo/'scripts/h62/item3/g52-differential'
    pins = {name: digest(source/name) for name in MODULES}
    require(summary.get('validator_sha256') == pins, 'changed/incomplete rejection validator closure')
    require(summary.get('reference_lock_sha256') == digest(repo/'tests/h62/item3/g52-differential/package-lock.json'), 'rejection SDK lock pin')
    require(type(summary.get('peak_aggregate_rss')) is int and
            0 < summary['peak_aggregate_rss'] <= 12*1024**3, 'internal rejection resource observation')
    expected = ['node', '--max-old-space-size=4096', RUNNER, str(bulk), label] + [str(n) for n in indices]
    require(command.get('command') == expected, 'unbound rejection command/indices')
    require('stopped' in command and command['stopped'] is None, 'stopped rejection run')
    external_bounds(command, source)
    require(isinstance(raw, bytes) and hashlib.sha256(raw).hexdigest() == summary.get('results_sha256'), 'rejection results hash')
    rows = [json.loads(line) for line in raw.splitlines()]
    require(len(rows) == len(indices), 'truncated/extra rejection rows')
    counts = Counter()
    for index, row in zip(indices, rows):
        require(isinstance(row, dict) and type(row.get('index')) is int and row['index'] == index and
                isinstance(row.get('path'), str) and isinstance(row.get('case'), str), 'rejection row identity/order')
        status = row.get('status')
        require(status in STATUSES, 'unknown rejection status')
        require(row.get('coverage_admitted') is False and row.get('engine_rpc_complete') is False and
                row.get('forkchoice_executed') is False and row.get('differential_complete') is False and
                row.get('source_semantics') == 'unsupported-adapter-pending' and
                type(row.get('source_matches')) is int and row['source_matches'] == 0,
                'conflated rejection row flags')
        if status == 'engine_error':
            require(row.get('retryable') is True, 'rejection error missing retryable marker')
        counts[status] += 1
    require(isinstance(summary.get('counts'), dict) and
            all(type(n) is int and n > 0 for n in summary['counts'].values()) and
            summary['counts'] == dict(counts), 'rejection status accounting')
    calls = summary.get('native_worker_calls')
    required_calls = counts['payload_rejection_reference_match'] + counts['payload_rejection_mismatch']
    require(type(calls) is int and required_calls <= calls <= required_calls + counts['engine_error'], 'rejection native call count')
    expected_exit = 1 if counts['engine_error'] or counts['payload_rejection_mismatch'] else 2
    require(type(command.get('exit')) is int and command['exit'] == expected_exit, 'wrong rejection exit')
    return rows


def read_captures(paths):
    """Hash the exact bytes inspected, never a second mutable file read."""
    buffers = {str(path): path.read_bytes() for path in paths}
    return buffers, {name: hashlib.sha256(raw).hexdigest() for name, raw in buffers.items()}


def audit(repo, bulk, label, command_path):
    from eest_export import verify_engine_x_inputs
    require(isinstance(label, str) and re.fullmatch('[a-z0-9-]+', label), 'invalid rejection label')
    summary_path = bulk/'evidence'/(label+'-summary.json')
    rows_path = bulk/'evidence'/(label+'.jsonl')
    buffers, captures = read_captures((summary_path, rows_path, command_path))
    summary = json.loads(buffers[str(summary_path)])
    command = json.loads(buffers[str(command_path)])
    raw = buffers[str(rows_path)]
    directory = Path(__file__).resolve().parent
    dependencies = {str(path): digest(path) for path in (Path(__file__).resolve(),
                    directory/'engine_execution_coverage.py', directory/'eest_export.py',
                    directory/'archive_census.py', directory/'pipeline.py')}
    rows = receipt_preflight(repo, bulk, label, summary, command, raw)
    binding = verify_engine_x_inputs(bulk)
    require(summary.get('archive_binding') == binding, 'rejection archive binding differs from regeneration')
    require(digest(bulk/'reference/package-lock.json') == summary['reference_lock_sha256'], 'installed rejection lock mismatch')
    wanted = {row['index']: row for row in rows}
    selected = {}
    with gzip.open(bulk/'engine-x-inputs.jsonl.gz', 'rt') as stream:
        for i, line in enumerate(stream):
            record = json.loads(line)
            require(type(record.get('index')) is int and record['index'] == i, 'noncanonical archived index')
            if i in wanted:
                require(record.get('status') == 'input-only-not-executed' and
                        (record.get('path'), record.get('case')) == (wanted[i]['path'], wanted[i]['case']), 'rejection identity differs from archive')
                selected[i] = record
            if len(selected) == len(wanted):
                break
    require(set(selected) == set(wanted), 'rejection selection absent from archive')
    for name, expected in binding['files'].items():
        require(digest(bulk/name) == expected, 'archive input changed during rejection preflight: '+name)
    for path, expected in {**captures, **dependencies}.items():
        require(digest(Path(path)) == expected, 'rejection capture changed during preflight')
    receipt_preflight(repo, bulk, label, summary, command, raw)
    return dict(schema=1, role='archive-identity-receipt-preflight-only', indices=summary['indices'],
                reported_status_counts=summary['counts'], archive_binding=binding,
                capture_sha256=captures, preflight_code_sha256=dependencies, checker_sha256=digest(Path(__file__)),
                native_evidence_checked=False, coverage_admitted=False, source_matches=0,
                differential_complete=False, full_conformance=False,
                remaining_checks=['canonical payload/conversion and allocation/genesis binding',
                                  'native category facts and full rollback/prefix continuity',
                                  'accepted transaction identities, integer gas/output/log observations',
                                  'unsupported-reason and worker-failure downgrade controls'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--bulk', type=Path, required=True)
    parser.add_argument('--label', required=True)
    parser.add_argument('--command', type=Path, required=True)
    args = parser.parse_args()
    repo, bulk = args.repo.resolve(), args.bulk.resolve()
    require(bulk != repo and repo not in bulk.parents, 'rejection bulk must stay outside repository')
    print(json.dumps(audit(repo, bulk, args.label, args.command.resolve()), indent=2))


if __name__ == '__main__':
    main()
