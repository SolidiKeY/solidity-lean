#!/usr/bin/env python3
"""Fault controls over real sealed proof evidence; no Lean success is mocked."""
import argparse
import copy
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile
from archive_io import read_json, require
import selected_accounting
import verify_combined


def run(repo):
    positive = verify_combined.verify(repo, 'selected')
    pin = read_json(repo / 'tests/h28-sol/mutation-testing/bulk-data.json', repo)['selected_proof_pack']
    data = Path(pin['archive']).read_bytes()
    require(len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256'], 'proof pack changed before fault controls')
    refused = []
    with tarfile.open(fileobj=io.BytesIO(data), mode='r:gz') as tar:
        members = {m.name for m in tar}
        cache = {}
        def original(name):
            if name not in cache: cache[name] = tar.extractfile(name).read()
            return cache[name]
        manifest = json.loads(original('run/manifest.json')); saved = json.loads(original('run/result.json'))
        faults = [('negative-object', 'unexpected or negative census object'),
                  ('missing-positive', 'unexpected or negative census object'),
                  ('empty-positive', 'empty positive census object'),
                  ('ledger-unit-omission', 'exhaustive ledger regeneration mismatch'),
                  ('fixture-theorem-omission', 'fixture theorem missing'),
                  ('missing-case-result', 'fixture references missing case result'),
                  ('zero-memory-profile', 'census resource bounds mismatch'),
                  ('version-swap', 'version gate resource bounds mismatch'),
                  ('version-failure', 'version gate resource bounds mismatch')]
        for fault, expected in faults:
            altered = {}; names = set(members); result = copy.deepcopy(saved)
            if fault == 'negative-object': names.add('census/InventoryNegative.olean')
            if fault == 'missing-positive': names.remove('census/InventoryAudit.olean')
            if fault == 'empty-positive': altered['census/InventoryAudit.olean'] = b''
            if fault == 'ledger-unit-omission':
                ledger = json.loads(original('ledger.json')); ledger['declarations'][0]['units'].pop()
                altered['ledger.json'] = json.dumps(ledger).encode()
            if fault == 'missing-case-result':
                fixture = json.loads(original('ledger.json'))['fixtures'][0]
                case_id = fixture['selected_roles'][0]['case_id']
                result['records'] = [r for r in result['records'] if r['id'] != case_id]
            if fault == 'fixture-theorem-omission':
                fixture = json.loads(original('ledger.json'))['fixtures'][0]
                case_id = fixture['selected_roles'][0]['case_id']; theorem = fixture['theorems'][0]
                record = next(r for r in result['records'] if r['id'] == case_id)
                for cert in record['validation'].values():
                    if 'all_owned_axioms' in cert:
                        cert['all_owned_axioms'] = {n: a for n, a in cert['all_owned_axioms'].items() if n.rsplit('.', 1)[-1] != theorem}
            if fault in {'zero-memory-profile', 'version-swap', 'version-failure'}:
                census = json.loads(original('census/result.json'))
                if fault == 'zero-memory-profile': census['checks']['positive']['memory_limit'] = 0
                if fault == 'version-swap': census['versions']['swap_limit'] = 1
                if fault == 'version-failure': census['versions']['failure'] = 'injected control failure'
                altered['census/result.json'] = json.dumps(census).encode()
            def read(name): return altered[name] if name in altered else original(name)
            try: selected_accounting.verify(repo, read, result, manifest, names)
            except ValueError as error:
                require(expected in str(error), 'fault rejected for an unrelated reason: ' + fault + ': ' + str(error))
                refused.append({'fault': fault, 'rejection': str(error)})
            else: raise ValueError('false pass for injected fault: ' + fault)
    return {'positive_replay': positive, 'expected_refusals': refused, 'fault_count': len(refused),
            'boundary': 'Saved real proof replay and deliberately corrupted metadata controls; no fresh Lean execution or mocked proof success.', 'scope_complete': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('output', type=Path); args = parser.parse_args()
    repo = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True).strip())
    require(not args.output.resolve().is_relative_to(repo), 'control results belong off Git')
    result = run(repo)
    with args.output.open('x') as stream: json.dump(result, stream, indent=2); stream.write('\n')
    print(json.dumps(result, indent=2))
