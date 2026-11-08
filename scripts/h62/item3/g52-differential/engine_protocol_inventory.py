#!/usr/bin/env python3
"""Inventory Engine-X protocol work without claiming execution.

Guarded regression: negative RPC expectations, version differences and malformed
request shapes must remain visible and never acquire payload/Source match credit
from offline block execution. The CLI reuses the existing archive verifier;
shape candidates below are metadata, not supported/executed fixtures.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
import re
from pathlib import Path

ALLOWED_KEYS = {'forkchoiceUpdatedVersion', 'newPayloadVersion', 'params'}


def request_profile(request):
    if not isinstance(request, dict):
        raise ValueError('request is not an object')
    issues = []
    extra = sorted(set(request) - ALLOWED_KEYS)
    if extra:
        issues.append('extra-request-fields')
    if not ((type(request.get('newPayloadVersion')) is int and request['newPayloadVersion'] == 4) or
            (type(request.get('newPayloadVersion')) is str and request['newPayloadVersion'] == '4')):
        issues.append('new-payload-version')
    if not ((type(request.get('forkchoiceUpdatedVersion')) is int and request['forkchoiceUpdatedVersion'] == 3) or
            (type(request.get('forkchoiceUpdatedVersion')) is str and request['forkchoiceUpdatedVersion'] == '3')):
        issues.append('forkchoice-version')
    params = request.get('params')
    if not isinstance(params, list) or len(params) != 4:
        issues.append('parameter-shape')
    else:
        if not isinstance(params[0], dict):
            issues.append('payload-object-shape')
        if not isinstance(params[1], list):
            issues.append('blob-hashes-shape')
        if not isinstance(params[2], str) or not re.fullmatch('0x[0-9a-f]{64}', params[2]):
            issues.append('beacon-root-shape')
        if not isinstance(params[3], list):
            issues.append('execution-requests-shape')
    return dict(extra_keys=extra, new_payload_version=request.get('newPayloadVersion'),
                forkchoice_version=request.get('forkchoiceUpdatedVersion'),
                parameter_count=len(params) if isinstance(params, list) else None,
                parameter_types=[type(value).__name__ for value in params] if isinstance(params, list) else None,
                issues=issues)


def inventory(records, expected):
    if type(expected) is not int or expected < 0:
        raise ValueError('invalid expected case count')
    rows = []
    profiles = Counter()
    requests_count = 0
    for i, record in enumerate(records):
        if (not isinstance(record, dict) or type(record.get('index')) is not int or
                record['index'] != i or i >= expected or
                not isinstance(record.get('path'), str) or not isinstance(record.get('case'), str)):
            raise ValueError('noncanonical case identity/order')
        fixture = record.get('fixture')
        if (not isinstance(fixture, dict) or fixture.get('network') != 'Osaka' or
                not isinstance(fixture.get('_info'), dict) or
                fixture['_info'].get('fixture-format') != 'blockchain_test_engine_x'):
            raise ValueError('unexpected fixture format/fork')
        requests = fixture.get('engineNewPayloads')
        if not isinstance(requests, list):
            raise ValueError('missing payload request list')
        details = [request_profile(request) for request in requests]
        issues = sorted({issue for detail in details for issue in detail['issues']})
        if not requests:
            issues.append('empty-payload-sequence')
        profiles['+'.join(issues) if issues else 'outer-envelope-candidate'] += 1
        requests_count += len(requests)
        rows.append(dict(index=i, path=record['path'], case=record['case'],
                         issues=issues, requests=details))
    if len(rows) != expected:
        raise ValueError('incomplete case inventory')
    return dict(schema=1, role='request-profile-inventory-only', cases=len(rows),
                requests=requests_count, case_profile_counts=dict(sorted(profiles.items())),
                candidate_scope='Outer envelope/basic positional types only; payload contents are not validated',
                executed_cases=0, source_matches=0, differential_complete=False, rows=rows)


def build(root):
    from eest_export import verify_engine_x_inputs
    binding = verify_engine_x_inputs(root)
    name = 'engine-x-inputs.jsonl.gz'
    with gzip.open(root/name, 'rt') as stream:
        result = inventory((json.loads(line) for line in stream), binding['cases'])
    with (root/name).open('rb') as source:
        if hashlib.file_digest(source, 'sha256').hexdigest() != binding['files'][name]:
            raise ValueError('input changed during inventory')
    result['archive_binding'] = binding
    result['generator_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bulk', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[4]
    root, output = args.bulk.resolve(), args.output.resolve()
    if root == repo or repo in root.parents or output == repo or repo in output.parents:
        parser.error('bulk and evidence output must stay outside repository')
    if output.exists():
        parser.error('output must be a new evidence file')
    result = build(root)
    with output.open('x') as target:
        target.write(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key not in ('rows', 'archive_binding')}, sort_keys=True))


if __name__ == '__main__':
    main()
