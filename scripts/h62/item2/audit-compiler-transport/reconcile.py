#!/usr/bin/env python3
"""Reconcile every source theorem with imported kernel declarations.

No positive witness is inferred from type parsing. Kernel-generated theorem
constants are included as separate uncovered records, not silently excluded.
"""
import argparse
from collections import defaultdict, Counter
import json
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('--census', type=Path, required=True)
ap.add_argument('--reflected', type=Path, required=True)
ap.add_argument('--output', type=Path, required=True)
ap.add_argument('--witness-metrics', type=Path)
a = ap.parse_args()
source = json.loads(a.census.read_text())
reflected = []
for path in sorted(a.reflected.glob('*.json')):
    reflected.extend(json.loads(path.read_text()))
by_source = defaultdict(list)
for row in reflected:
    by_source[(row['module'].replace('.', '/')+'.lean', row['source_name'])].append(row)
verified = False
if a.witness_metrics and a.witness_metrics.exists():
    validation = json.loads(a.witness_metrics.read_text())
    verified = validation['exit'] == 0 and not validation['stop_reason']
positive = {
    'Solidity.Backend.Passes.'+name for name in
    ('compilation_exact', 'compilation_success', 'compilation_reflect_success',
     'compilation_revert_iff', 'compilation_input_stack')}
negative = {
    'Solidity.Backend.Passes.P12MemoryCapture.nonempty_revert_incompatible': 'memory_joint_impossible',
    'Solidity.Backend.Passes.P12StorageCapture.nonempty_revert_incompatible': 'storage_joint_impossible'}
records, consumed, missing = [], set(), []
module_owners = {}
for r in source['modules']:
    path = r['module']
    key = 'V12' if '/InternalFlow/' in path else 'VO1' if path.startswith('Solidity/Optimizer/') else 'V09'
    module_owners[path] = (key, {'V09':'v07-v11/v09-compiler-passes', 'V12':'v12-v17/v12-flow-calls', 'VO1':'solidity-fullscope-20261104/vo1-optimizer'}[key])
for original in source['statements']:
    matches = by_source[(original['module'], original['source_name'])]
    if len(matches) != 1:
        missing.append({'id': original['id'], 'matches': len(matches)})
        continue
    row = dict(original, **matches[0])
    consumed.add(row['kernel_name'])
    row['origin'] = 'explicit-source-theorem'
    row['witness_status'] = 'uncovered'
    if row['source_name'] in positive:
        row['witness_status'] = 'verified-joint-witness' if verified else 'prepared-joint-witness'
        row['audit_theorem'] = 'H62.CompilerTransport.boundary_joint_witness'
        row['joint_witness'] = row['audit_theorem'] if verified else None
        row['input_feasibility'] = ('verified simultaneously by ' if verified else 'prepared in ') + row['audit_theorem']
        row['global_premises'] = ('Per-program Compilation certificate inhabited in the same tuple; no global P12 producer is required or instantiated.' if verified else 'Prepared per-program certificate tuple; no inhabitation is certified and no global P12 producer is instantiated.')
    elif row['source_name'] in negative:
        row['witness_status'] = 'verified-joint-impossibility' if verified else 'prepared-joint-impossibility'
        row['audit_theorem'] = 'H62.CompilerTransport.'+negative[row['source_name']]
        row['impossibility_certificate'] = row['audit_theorem'] if verified else None
        row['input_feasibility'] = 'jointly infeasible under the exact frozen hypotheses' if verified else 'joint impossibility certificate prepared'
        row['global_premises'] = 'Joint incompatibility does not establish any individual global producer structure uninhabited.'
    elif original['false_conclusion']:
        row['witness_status'] = 'intentional-private-negative; universal-witness-criterion-conflict'
    row['global_input_classification'] = ('Per-program Compilation certificate plus joint physical Input/source/target execution tuple; no global P12 producer is instantiated.' if row['source_name'] in positive else 'pending semantic review; binder Prop/data alone is insufficient')
    records.append(row)
for row in reflected:
    if row['kernel_name'] in consumed: continue
    path = row['module'].replace('.', '/')+'.lean'
    owner_key, owner = module_owners[path]
    records.append(dict(row, id=path+'::'+row['kernel_name'], origin='kernel-generated-theorem',
                        owner_key=owner_key, owner=owner, witness_status='uncovered',
                        global_input_classification='pending semantic review'))
ids = [r['kernel_name'] for r in records]
assert len(ids) == len(set(ids)), 'duplicate kernel identity'
result = {'base': source['base'], 'missing_or_ambiguous_source_declarations': missing,
          'summary': {'source_theorems': len(source['statements']), 'kernel_theorems': len(reflected),
                      'records': len(records), 'source_matches': len(consumed),
                      'statuses': dict(Counter(r['witness_status'] for r in records)),
                      'positive_witness_validation_passed': verified},
          'boundary': 'No global-premise or per-input feasibility claim follows from reflection. '
                      'Negative certificates do not satisfy the literal positive-witness requirement.',
          'statements': records}
a.output.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
print(json.dumps(result['summary'], sort_keys=True))
if missing:
    print(json.dumps(missing, ensure_ascii=False))
    raise SystemExit(1)
if len(consumed) != len(source['statements']): raise SystemExit(1)
print('PASS: each frozen source theorem matched exactly once; generated theorem constants explicitly accounted')
