#!/usr/bin/env python3
"""Guarded regression: archive preflight or reported rejection labels alone must
not qualify empty, input-unbound or malformed native artifacts. Only all-match
jobs pass this initial reference-artifact qualifier; every error/unsupported job
stays unqualified by default. Explicit matching-subset mode keeps failures raw and
propagates their job exit. No native execution, positive coverage, RPC or Source credit.
"""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
from engine_execution_coverage import digest, require, exact_nat
from engine_rejection_preflight import audit, read_captures


def original_items(path, rows, expected_sha):
    """Hash exactly the compressed bytes consumed, including the unread tail."""
    wanted = {row['index']: row for row in rows}
    selected = []
    hasher = hashlib.sha256()
    with path.open('rb') as raw:
        class HashedReader:
            def read(self, size=-1):
                chunk = raw.read(size)
                hasher.update(chunk)
                return chunk
        reader = HashedReader()
        with gzip.GzipFile(fileobj=reader, mode='rb') as compressed:
            with io.TextIOWrapper(compressed) as source:
                for index, line in enumerate(source):
                    record = json.loads(line)
                    require(type(record.get('index')) is int and record['index'] == index, 'noncanonical original input index')
                    if index in wanted:
                        row = wanted[index]
                        require((record['path'], record['case']) == (row['path'], row['case']), 'qualification input identity mismatch')
                        selected.append(dict(record=record, row=row))
                    if len(selected) == len(rows):
                        break
        while reader.read(1024*1024):
            pass
    require(hasher.hexdigest() == expected_sha, 'consumed input bytes differ from pinned archive')
    require(len(selected) == len(rows), 'qualification input selection incomplete')
    return selected


def validate_observed_integer_types(rows):
    """Preserve JSON integer types before the JS decoder can normalize 3.0."""
    for row in rows:
        native = row['native']
        require(type(native.get('steps')) is int and type(native.get('max_rlp_block_size')) is int,
                'noncanonical native step/block-size integer')
        exact_nat(native['steps'], 'steps')
        for field in ('payload_versions', 'forkchoice_version'):
            require(type(row['binding'].get(field)) is int, 'noncanonical payload binding version integer')
        if 'raw_payload_indices' in row['binding']:
            require(isinstance(row['binding']['raw_payload_indices'], list) and
                    all(type(n) is int and n >= 0 for n in row['binding']['raw_payload_indices']),
                    'noncanonical raw payload index integer')
        for expected in row['expected']:
            require(type(expected.get('block_index')) is int, 'noncanonical expected rejection index')
        for rejection in native['rejections']:
            require(type(rejection.get('block_index')) is int, 'noncanonical native rejection index')
            if 'transaction_index' in rejection['validation_facts']:
                require(type(rejection['validation_facts']['transaction_index']) is int and
                        rejection['validation_facts']['transaction_index'] >= 0,
                        'noncanonical decode transaction index')
            if 'transactionType' in rejection['validation_facts']:
                require(type(rejection['validation_facts']['transactionType']) is int,
                        'noncanonical rejection transaction type')
        for block in native['blocks']:
            for field in ('number', 'gas_used'):
                exact_nat(block[field], field)
            for tx in block['transactions']:
                require(all(type(tx.get(field)) is int for field in ('index', 'type', 'receipt_status')),
                        'noncanonical transaction integer identity/status')
                for field in ('gas_limit', 'receipt_cumulative_gas_used', 'total_gas_spent',
                              'execution_gas_used', 'native_gas_refund_counter'):
                    exact_nat(tx[field], field)


def validate_metrics(items, selected):
    require(isinstance(items, list) and len(items) == len(selected), 'evidence checker selection mismatch')
    for item, original in zip(items, selected):
        record, row = original['record'], original['row']
        require(all(type(item.get(key)) is int and item[key] >= 0 for key in
                    ('index', 'qualified_rejections', 'accepted_prefix_blocks',
                     'transaction_observations', 'raw_log_entries', 'steps')),
                'noncanonical evidence metrics')
        requests = record['fixture']['engineNewPayloads']
        rejected = [q for q in requests if 'validationError' in q]
        accepted = [q for q in requests if 'validationError' not in q]
        expected = dict(index=record['index'], qualified_rejections=len(rejected),
                        accepted_prefix_blocks=len(accepted),
                        transaction_observations=sum(len(q['params'][0]['transactions']) for q in accepted),
                        raw_log_entries=sum(len(tx['logs']) for block in row['native']['blocks'] for tx in block['transactions']),
                        steps=row['native']['steps'])
        require(item == expected and expected['qualified_rejections'] > 0,
                'evidence metrics differ from original inputs/captured observations')


def matching_subset(rows, allow_partial=False):
    """Never treat unsupported/error rows as qualified or hide failed job exits."""
    matches = [row for row in rows if row['status'] == 'payload_rejection_reference_match']
    if not allow_partial:
        require(len(matches) == len(rows), 'nonmatch/error/unsupported job remains unqualified')
    else:
        require(all(row['status'] in ('payload_rejection_reference_match', 'engine_error',
                                     'payload_rejection_mismatch') for row in rows),
                'unsupported job remains unqualified; no failure downgrade')
    require(matches, 'job has no matching artifacts to qualify')
    return matches


def qualify(repo, bulk, label, command_path):
    return _qualify(repo, bulk, label, command_path, False)


def qualify_matches(repo, bulk, label, command_path):
    return _qualify(repo, bulk, label, command_path, True)


def _qualify(repo, bulk, label, command_path, allow_partial):
    directory = Path(__file__).resolve().parent
    modules = ('engine_rejection_qualification.py', 'engine_rejection_evidence.mjs',
               'engine_rejection_preflight.py', 'engine_execution_coverage.py')
    checker_pins = {name: digest(directory/name) for name in modules}
    preflight = audit(repo, bulk, label, command_path)
    paths = [Path(name) for name in preflight['capture_sha256']]
    buffers, captures = read_captures(paths)
    require(captures == preflight['capture_sha256'], 'capture changed after archive preflight')
    rows_path = bulk/'evidence'/(label+'.jsonl')
    rows = [json.loads(line) for line in buffers[str(rows_path)].splitlines()]
    all_rows = rows
    rows = matching_subset(all_rows, allow_partial)
    validate_observed_integer_types(rows)
    all_items = original_items(bulk/'engine-x-inputs.jsonl.gz', all_rows,
                               preflight['archive_binding']['files']['engine-x-inputs.jsonl.gz'])
    selected = [item for item in all_items if item['row']['status'] == 'payload_rejection_reference_match']
    checked = subprocess.run(['node', '--max-old-space-size=4096',
                              str(directory/'engine_rejection_evidence.mjs'), str(bulk)],
                             input=json.dumps(selected), text=True, capture_output=True,
                             cwd=repo, timeout=60, check=True)
    evidence = json.loads(checked.stdout)
    require(evidence.get('role') == 'native-artifact-consistency-only' and
            type(evidence.get('new_native_executions')) is int and evidence['new_native_executions'] == 0 and
            type(evidence.get('source_matches')) is int and evidence['source_matches'] == 0 and
            evidence.get('engine_rpc_complete') is False and evidence.get('full_conformance') is False,
            'evidence checker conflated execution/source/conformance')
    metrics = evidence.get('items')
    validate_metrics(metrics, selected)
    for name, expected in preflight['archive_binding']['files'].items():
        require(digest(bulk/name) == expected, 'archive input changed during evidence check')
    for name, expected in {**preflight['capture_sha256'], **preflight['preflight_code_sha256']}.items():
        require(digest(Path(name)) == expected, 'capture/preflight dependency changed during evidence check')
    summary = json.loads(buffers[str(bulk/'evidence'/(label+'-summary.json'))])
    for name, expected in summary['validator_sha256'].items():
        require(digest(directory/name) == expected, 'runtime validator changed during evidence check')
    require(digest(bulk/'reference/package-lock.json') == summary['reference_lock_sha256'], 'SDK lock changed during evidence check')
    for name, expected in checker_pins.items():
        require(digest(directory/name) == expected, 'qualification checker changed during execution')
    result = dict(schema=1, role='qualified-reference-rejection-artifacts-only',
                indices=[row['index'] for row in rows], qualified_rejection_cases=len(rows),
                qualified_rejections=sum(x['qualified_rejections'] for x in metrics),
                accepted_prefix_blocks=sum(x['accepted_prefix_blocks'] for x in metrics),
                transaction_observations=sum(x['transaction_observations'] for x in metrics),
                raw_log_entries=sum(x['raw_log_entries'] for x in metrics),
                steps=sum(x['steps'] for x in metrics), checker_sha256=checker_pins,
                preflight=preflight, native_artifact_evidence_checked=True,
                new_native_executions=0, positive_payload_coverage_delta=0,
                engine_rpc_complete=False, full_conformance=False, source_matches=0,
                differential_complete=False, runtime_gate_pass=False)
    if allow_partial:
        command = json.loads(buffers[str(command_path)])
        result.update(role='qualified-reference-rejection-matching-subset-only',
                      original_indices=preflight['indices'],
                      original_status_counts=preflight['reported_status_counts'],
                      original_job_exit=command['exit'], propagated_exit=command['exit'],
                      unqualified_rows=[row for row in all_rows if row['status'] != 'payload_rejection_reference_match'],
                      unqualified_indices=[row['index'] for row in all_rows if row['status'] != 'payload_rejection_reference_match'],
                      retryable_indices=[row['index'] for row in all_rows if row['status'] == 'engine_error'])
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--bulk', type=Path, required=True)
    parser.add_argument('--label', required=True)
    parser.add_argument('--command', type=Path, required=True)
    parser.add_argument('--matches-only', action='store_true', help='qualify matching subset; preserve every failed job exit and raw nonmatch row')
    args = parser.parse_args()
    function = qualify_matches if args.matches_only else qualify
    result = function(args.repo.resolve(), args.bulk.resolve(), args.label, args.command.resolve())
    print(json.dumps(result, indent=2))
    return result.get('propagated_exit', 2)


if __name__ == '__main__':
    raise SystemExit(main())
