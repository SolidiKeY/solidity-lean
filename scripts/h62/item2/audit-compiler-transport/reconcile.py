#!/usr/bin/env python3
"""Once-only frozen-source reconciliation with checked H69 audit evidence.

Syntactic premise tuples, intentional impossibility, semantic input feasibility,
and proof-bearing data producers remain distinct. Search failure is uncovered.
"""
import argparse
from collections import defaultdict, Counter
import hashlib
import json
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('--census', type=Path, required=True)
ap.add_argument('--reflected', type=Path, required=True)
ap.add_argument('--output', type=Path, required=True)
ap.add_argument('--witness-metrics', type=Path, required=True)
ap.add_argument('--h69', type=Path, required=True)
ap.add_argument('--classification', type=Path, default=Path('tests/h62/item2/audit-compiler-transport/h69-classification.json'))
a = ap.parse_args()
load = lambda p: json.loads(p.read_text())
def passed(path):
    r = load(path)
    assert r['exit'] == 0 and not r['stop_reason'], path
    assert not any(t in Path(r['log']).read_text() for t in ['error:', 'PANIC', 'sorryAx']), path
    return r
source = load(a.census)
reflected = [r for p in sorted(a.reflected.glob('*.json')) for r in load(p)]
passed(a.h69/'reflection.json')
passed(a.witness_metrics)
passed(a.h69/'check-H69.json')
passed(a.h69/'check-ExplicitCases.json')
classification = load(a.classification)
assert classification['decision'] == 'H69'
negative = {r['source_name']: r for r in classification['negative_controls']}
assert len(negative) == len(classification['negative_controls']) == 68
inventory = {r['kernel_name']: r for r in load(a.h69/'generated/inventory.json')}
assert set(inventory) == {r['kernel_name'] for r in reflected}
metrics = [json.loads(line) for line in (a.h69/'generated/metrics.jsonl').read_text().splitlines()]
expected_drivers = [a.h69/'generated/EmptyWitnesses.lean', a.h69/'generated/NegativeWitnesses.lean'] + [Path(p) for p in load(a.h69/'generated/batches.json')]
assert len(metrics) == len(expected_drivers)
for metric, driver in zip(metrics, expected_drivers):
    assert metric['exit'] == 0 and not metric['stop_reason'] and metric['clean_diagnostics']
    assert metric['command'][-1] == str(driver.resolve())
    assert metric['source_sha256'] == hashlib.sha256(driver.read_bytes()).hexdigest()
    assert not any(t in Path(metric['log']).read_text() for t in ['error:', 'PANIC', 'sorryAx'])
positive = {'Solidity.Backend.Passes.'+n for n in ('compilation_exact', 'compilation_success', 'compilation_reflect_success', 'compilation_revert_iff', 'compilation_input_stack')}
by_source = defaultdict(list)
for row in reflected:
    by_source[(row['module'].replace('.', '/')+'.lean', row['source_name'])].append(row)
records, consumed, missing = [], set(), []
for original in source['statements']:
    matches = by_source[(original['module'], original['source_name'])]
    if len(matches) != 1:
        missing.append({'id': original['id'], 'matches': len(matches)})
        continue
    row = dict(original, **matches[0])
    row['origin'] = 'explicit-source-theorem'
    consumed.add(row['kernel_name'])
    records.append(row)
for original in reflected:
    if original['kernel_name'] in consumed: continue
    row = dict(original)
    path = row['module'].replace('.', '/')+'.lean'
    key = 'V12' if '/InternalFlow/' in path else 'VO1' if path.startswith('Solidity/Optimizer/') else 'V09'
    row.update(id=path+'::'+row['kernel_name'], owner_key=key,
               owner={'V09':'v07-v11/v09-compiler-passes', 'V12':'v12-v17/v12-flow-calls', 'VO1':'solidity-fullscope-20261104/vo1-optimizer'}[key])
    row['origin'] = ('semantic-proof-field-projection' if row['proof_field_projection'] else
                     'proof-valued-definition' if row['declaration_kind'] != 'theorem' else 'derived-theorem-constant')
    records.append(row)
for row in records:
    item = inventory[row['kernel_name']]
    assert item['source_type_sha256'] == hashlib.sha256(row['raw_type'].encode()).hexdigest()
    row['global_input_classification'] = 'pending semantic review; a syntactic telescope witness does not prove every defined universal domain inhabited'
    row['witness_status'] = 'uncovered'
    name = row['source_name']
    if name in negative:
        record = negative[name]
        row.update(witness_status='checked-intentional-joint-impossibility', audit_theorem=record['proof'],
                   intentional_negative=record['why_intentional'], decision='H69')
        if record.get('declaration_role'):
            assert record['source_type_sha256'] == item['source_type_sha256']
            row['ordinary_parent_obligation'] = record['parent_source_name']
    elif name in positive:
        row.update(witness_status='checked-correlated-joint-witness', audit_theorem='H62.CompilerTransport.boundary_joint_witness',
                   global_input_classification='same per-program Compilation, physical Input, source and target execution tuple; no global P12 producer instantiated')
    elif item['mode'] == 'empty-external-telescope':
        assert not row['binders']
        row.update(witness_status='checked-empty-syntactic-premise-tuple', audit_theorem=item['proof'])
    elif item['mode'] == 'bounded-constructive-search':
        result = load(Path(item['result_file']))
        assert result['source'] == row['kernel_name']
        if result['status'] == 'checked-declaration':
            assert result['proof'] == item['proof']
            assert result['universe_parameters'] == row['level_parameters']
            assert set(result['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
            row.update(witness_status='checked-syntactic-joint-witness', audit_theorem=result['proof'], witness_bindings=result['bindings'], axioms=result['axioms'])
        else:
            assert result['status'] == 'unresolved'
            row['unresolved_reason'] = result['reason']
# Preserve scanner metadata as explicitly provisional observations, then assign
# audit-qualified fields without upgrading syntactic tuples to semantic domains.
for row in records:
    for key in ['joint_witness', 'input_feasibility', 'global_premises']:
        if key in row:
            row['source_scan_'+key] = row.pop(key)
    status = row['witness_status']
    row['joint_witness'] = None
    row['impossibility_certificate'] = None
    row['global_premises'] = row['global_input_classification']
    if status == 'checked-intentional-joint-impossibility':
        row['impossibility_certificate'] = row['audit_theorem']
        row['input_feasibility'] = 'original complete tuple jointly impossible; accepted deliberate negative under H69'
    elif status == 'checked-correlated-joint-witness':
        row['joint_witness'] = row['audit_theorem']
        row['input_feasibility'] = 'checked simultaneous per-program certificate and physical execution tuple'
    elif status in ['checked-syntactic-joint-witness', 'checked-empty-syntactic-premise-tuple']:
        row['joint_witness'] = row['audit_theorem']
        row['input_feasibility'] = ('checked empty original syntactic telescope; defined semantic domains still pending' if status == 'checked-empty-syntactic-premise-tuple' else 'checked original syntactic telescope tuple; global/input semantic review still pending')
    else:
        row['input_feasibility'] = 'uncovered; no joint tuple certified'
ids = [r['kernel_name'] for r in records]
assert len(ids) == len(set(ids)) == len(reflected)
assert not missing and len(consumed) == len(source['statements'])
assert {r['source_name'] for r in records if r.get('decision') == 'H69'} == set(negative)
carriers = [r for p in sorted((a.h69/'carriers').glob('*.json')) for r in load(p)]
passed(a.h69/'carriers.json')
assert len({r['kernel_name'] for r in carriers}) == len(carriers)
result = {'base': source['base'], 'decision': 'H69; Q-NEG-01 resolved; no statement changed',
 'missing_or_ambiguous_source_declarations': missing,
 'summary': {'source_theorems':len(source['statements']), 'source_matches':len(consumed),
  'proof_constants':len(reflected), 'records':len(records),
  'declaration_kinds':dict(Counter(r['declaration_kind'] for r in records)),
  'origins':dict(Counter(r['origin'] for r in records)),
  'statuses':dict(Counter(r['witness_status'] for r in records)),
  'proof_bearing_data_producers':len(carriers), 'producer_joint_domain_audit':'pending'},
 'boundary':'Empty tuples check only original syntactic telescopes. Defined universal predicates and proof-bearing data producers need semantic/domain audit. No automatic gas/fork, producer inhabitation or compiler-totality conclusion. Intentional impossibility is accepted only for the explicit H69 registry; ordinary parents stay independent.',
 'supplementary_uniform_nonempty_cases':['H62.CompilerTransport.ExplicitCases.pipeline_joint_nonempty','H62.CompilerTransport.ExplicitCases.guarded_pipeline_joint_nonempty'],
 'proof_bearing_data_producers':carriers, 'statements':records}
a.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(result['summary'],sort_keys=True))
print('PASS frozen-source once-only fidelity and checked evidence reconciliation; semantic/full coverage remains incomplete')
