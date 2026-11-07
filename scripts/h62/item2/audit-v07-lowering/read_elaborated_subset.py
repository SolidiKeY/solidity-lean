#!/usr/bin/env python3
"""Validate generic inspector completion and associate only exact source names.

Guarded regression: partial logs, generated constants, or proof/data guesses must
not be counted as a completed mapped-theorem telescope export. This records
live binder types, not simultaneous feasibility or semantic classifications.
"""
import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path


def sha(data):
    return hashlib.sha256(data).hexdigest()


def decode(log, pins):
    rows, done = [], []
    for line in log.splitlines():
        if line.startswith('H62_CENSUS_JSON '):
            rows.append(json.loads(line.removeprefix('H62_CENSUS_JSON ')))
        elif line.startswith('H62_CENSUS_DONE '):
            done.append(json.loads(line.removeprefix('H62_CENSUS_DONE ')))
    if len(done) != 1:
        raise ValueError('missing or duplicate completion marker')
    names = [r['name'] for r in rows]
    if len(set(names)) != len(names):
        raise ValueError('duplicate constant identity')
    for record in [*rows, *done]:
        if record['manifest_sha256'] != pins['manifest_sha256']:
            raise ValueError('manifest fingerprint mismatch')
    counts = Counter(r['module'] for r in rows)
    observed = {module: counts[module] for module in pins['modules']}
    if not set(counts) <= set(pins['modules']) or observed != done[0]['counts']:
        raise ValueError('module completion count mismatch')
    return rows


def check_pins(repo, folder):
    pins = json.loads((folder/'pins.json').read_text())
    core = {key:pins[key] for key in ['base','modules','source_sha256','inspection_template_sha256']}
    fingerprint = sha(json.dumps(core, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode())
    if fingerprint != pins['manifest_sha256']:
        raise ValueError('pin fingerprint mismatch')
    if {m.replace('.', '/')+'.lean' for m in pins['modules']} != set(pins['source_sha256']):
        raise ValueError('pin module/path mismatch')
    provider = (repo/pins['template_provider']).read_bytes()
    if sha(provider) != pins['template_provider_sha256']:
        raise ValueError('inspection provider changed')
    nodes = [n for n in ast.parse(provider).body if isinstance(n, ast.Assign)
             and any(isinstance(t, ast.Name) and t.id=='TEMPLATE' for t in n.targets)]
    if len(nodes) != 1:
        raise ValueError('inspection template missing')
    template = ast.literal_eval(nodes[0].value)
    if sha(template.encode()) != pins['inspection_template_sha256']:
        raise ValueError('inspection template changed')
    expected = ('import Lean\n'+''.join('import '+m+'\n' for m in pins['modules'])+
                template.replace('MODULES', ', '.join('`'+m for m in pins['modules'])).replace('FINGERPRINT', fingerprint))
    probe = (folder/'Probe.lean').read_bytes()
    if probe != expected.encode() or sha(probe) != pins['inspection_sha256']:
        raise ValueError('inspection source changed')
    for path, expected_hash in pins['source_sha256'].items():
        if sha((repo/path).read_bytes()) != expected_hash:
            raise ValueError('producer changed')
    binding = dict(pins_sha256=sha((folder/'pins.json').read_bytes()),
                   inspection_sha256=sha(probe), source_sha256=pins['source_sha256'],
                   template_provider_sha256=sha(provider))
    return pins, binding


def validate_execution(text, gate, expected_command, binding):
    if gate.get('exit') != 0 or gate.get('process_exit') != 0 or gate.get('resource_stop') is not False:
        raise ValueError('unsuccessful execution receipt')
    limits = dict(memory_max=12*1024**3, memory_swap_max=0, lean_num_threads=1)
    if gate.get('limits') != limits or gate.get('minimum_parent_headroom_bytes', 0) < 4*1024**3:
        raise ValueError('execution resource policy mismatch')
    if gate.get('command') != expected_command:
        raise ValueError('execution command mismatch')
    stages = [json.loads(line.removeprefix('H62_SOURCE_BINDING '))
              for line in text.splitlines() if line.startswith('H62_SOURCE_BINDING ')]
    if stages != [dict(stage='before', **binding), dict(stage='after', **binding)]:
        raise ValueError('execution source binding mismatch')


def inspect(repo, folder, log, inventory, gate_path):
    pins, binding = check_pins(repo, folder)
    text = log.read_text()
    gate = json.loads(gate_path.read_text())
    command = ['python3', str(repo/'scripts/h62/item2/audit-v07-lowering/run_elaborated_subset.py'),
               '--repo', str(repo), '--folder', str(folder)]
    validate_execution(text, gate, command, binding)
    if Path(gate['log']).resolve() != log.resolve():
        raise ValueError('execution log path mismatch')
    raw = inventory.read_bytes()
    if sha(raw) != pins['inventory_sha256']:
        raise ValueError('inventory changed')
    for path, expected in pins['source_sha256'].items():
        if sha((repo/path).read_bytes()) != expected:
            raise ValueError('producer changed')
    rows = decode(log.read_text(), pins)
    by_name = {r['name']: r for r in rows}
    ledger = json.loads(raw)
    selected = set(pins['source_sha256'])
    originals = [r for r in ledger['theorems'] if r['path'] in selected]
    matched = []
    for old in originals:
        name = old['source_qualified_name']
        record = by_name.get(name)
        if record is None or not record['is_theorem'] or not record['proof_type']:
            raise ValueError('mapped theorem not exported as proof: '+name)
        if record['module'].replace('.', '/')+'.lean' != old['path']:
            raise ValueError('mapped theorem module mismatch')
        if old['module_sha256'] != pins['source_sha256'][old['path']]:
            raise ValueError('mapped theorem source mismatch')
        matched.append(dict(name=name, path=old['path'], source_signature_sha256=old['signature_sha256'],
                            type_expr_sha256=sha(record['type_expr'].encode()),
                            binders=record['binders'], type=record['type'],
                            feasibility='pending', semantic_classification='pending'))
    return dict(schema_version=1, boundary='Successful live subset inspection; not original migration fidelity, whole census or feasibility acceptance.',
                gate_receipt_sha256=sha(gate_path.read_bytes()),
                manifest_sha256=pins['manifest_sha256'], raw_log_sha256=sha(log.read_bytes()),
                selected_modules=pins['modules'], total_exported_constants=len(rows),
                matched_source_theorems=len(matched), generated_or_other_constants=len(rows)-len(matched),
                binder_count=sum(len(r['binders']) for r in matched),
                proof_binder_count=sum(b['proof_binder'] for r in matched for b in r['binders']),
                statements=matched)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['repo', 'folder', 'log', 'inventory', 'gate', 'output']:
        parser.add_argument('--'+name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.resolve().is_relative_to(args.repo.resolve()):
        raise ValueError('external output required')
    if args.output.exists():
        raise FileExistsError('existing output refused')
    result = inspect(args.repo.resolve(), args.folder.resolve(), args.log, args.inventory, args.gate)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'statements'}, indent=2))
