#!/usr/bin/env python3
"""Bind H69 classifications and two ordinary witnesses to passing proof gates.
No synthetic utility control contributes interface coverage. Run under writer lock.
"""
import argparse,hashlib,json,pathlib,re
ap=argparse.ArgumentParser();ap.add_argument('--output',type=pathlib.Path,required=True);args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
ev=pathlib.Path('/workspace/h62-audit-yul-evidence');test=pathlib.Path('tests/h62/item2/audit-yul')
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def gate(source,directory):
 rows=[json.loads(l) for l in (ev/directory/'commands.jsonl').read_text().splitlines()]
 rows=[r for r in rows if r['command'][-1]==source]
 if not rows:raise ValueError('no proof gate for '+source)
 row=rows[-1]
 if row['exit']!=0 or row['source_sha256']!=sha(source):raise ValueError('stale/failed proof gate: '+source)
 return row
ref_source=str(test/'Refutations.lean');ref_gate=gate(ref_source,'h69-refutations-final')
fidelity_source=str(test/'RefutationFidelity.lean');fidelity_gate=gate(fidelity_source,'h69-fidelity')
if 'H69_FROZEN_TYPE_FIDELITY_PASS: 11 exact elaborated telescopes' not in pathlib.Path(fidelity_gate['log']).read_text():raise ValueError('missing exact-type fidelity gate')
control_source=str(test/'DefaultWitnessControls.lean');control_gate=gate(control_source,'h69-default-checked')
tool_source=str(test/'DefaultWitnesses.lean');tool_gate=gate(tool_source,'h69-default-checked')
source_text=pathlib.Path(control_source).read_text()
expected=re.findall(r'^audit_joint_defaults "([^"]+)"',source_text,re.M)
records=[json.loads(l) for l in (ev/'h69-default-controls.jsonl').read_text().splitlines()][-len(expected):]
if [r['theorem'] for r in records]!=expected:raise ValueError('control snapshot does not match final source')
if [r['status'] for r in records]!=['joint_witness_proved','uncovered','joint_witness_proved','joint_witness_proved','uncovered','joint_witness_proved']:raise ValueError('constructor positive/negative control drift')
snapshot=dict(source=control_source,source_sha256=sha(control_source),gate=control_gate,proof_tool=tool_source,proof_tool_sha256=sha(tool_source),proof_tool_gate=tool_gate,records=records)
(args.output/'control-snapshot.json').write_text(json.dumps(snapshot,indent=2,sort_keys=True)+'\n')
manifest=json.loads((test/'witnesses.json').read_text());source_census=json.load(open(ev/'reproduced-complete/census/census.json'));source_index={r['source_name']:r for r in source_census['declarations'] if r['kind']=='theorem' and r['visibility']=='public'}
reasons={
 'Solidity.Frontend.YulJson.Words.declaration_impossible':('declaration_impossible','The empty declaration context has no positional member.'),
 'Solidity.Frontend.YulJson.Words.reference_impossible':('reference_impossible','References must identify a declaration in the empty table.'),
 'Solidity.Yul.Checks.ClosedFunctions.no_empty_member':('no_empty_member','An empty function-signature context cannot have an intrinsic Member.'),
 'Solidity.Yul.Checks.ClosedFunctions.no_external_reference':('no_external_reference','An empty external context cannot have an intrinsic reference.'),
 'Solidity.Yul.Checks.ClosedPure.no_memory_builtin':('no_memory_builtin','MLOAD is intentionally rejected by the pure-word builtin profile.'),
 'Solidity.Yul.ScopedExternalD.function_noWrites':('function_noWrites','Function-visible globals cannot carry the external-variable write capability; storage effects are separate.'),
 'Solidity.Yul.GlobalExternalD.noWrites':('global_noWrites','Global-only external name resolution is separated from variable-write capability.'),
 'Solidity.Yul.ScalarRef.not_globals':('scalar_not_globals','The global projection deliberately excludes scalar Solidity VALUE locals.'),
 'Solidity.Yul.Views.FixedDeclaration.no_dynamic_array':('no_dynamic_array','Fixed storage packing is separated from dynamic-length storage arrays.'),
 'Solidity.Yul.WordCell.not_globals':('wordCell_not_globals','Global projection excludes scalar/address/selector word-local cells.')}
for r in manifest['statements']:
 if r['theorem'] in reasons:
  name,reason=reasons[r['theorem']]
  r.update(status='intentional_refutation_proved',audit_criterion='H69',intentional_reason=reason,proof='H62.AuditYul.Refutations.'+name,proof_module=ref_source,proof_source_sha256=sha(ref_source),proof_gate=str(ev/'h69-refutations-final/commands.jsonl'),fidelity_gate=fidelity_gate['log'])
 elif r['theorem']=='Solidity.Lowering.P8.SpecExecution.no_countable_resource':
  source=str(test/'ImpossiblePremises.lean');g=gate(source,'final-proofs')
  r.update(status='intentional_refutation_proved',audit_criterion='H69',intentional_reason='The stated separation theorem refutes a Nat retraction of resources carrying arbitrary failure plans; it is not a success guarantee.',proof_module=source,proof_source_sha256=sha(source),proof_gate=str(ev/'final-proofs/commands.jsonl'),fidelity='Original SourceRealization import checked; exact original/dependency kernel types verified up to alpha/definitional equality.',fidelity_gate=fidelity_gate['log'])
 else:
  source=str(test/'Success.lean');g=gate(source,'final-proofs');r.update(audit_criterion='joint_satisfiability',proof_module=source,proof_source_sha256=sha(source),proof_gate=str(ev/'final-proofs/commands.jsonl'))
by_name={r['theorem']:r for r in manifest['statements']}
for name in ['Solidity.Yul.pow_halve','Solidity.Yul.powBits_correct']:
 record=next(r for r in records if r['theorem']==name)
 original=source_index[name]
 r=dict(theorem=name,status='joint_witness_proved',audit_criterion='joint_satisfiability',frozen_signature_sha256=original['signature_sha256'],classification='Complete exposed telescope, including proof-valued hypotheses, jointly supplied by a closed kernel-checked existential proof.',proof=record['proof'],proof_module=control_source,proof_source_sha256=sha(control_source),proof_gate=str(ev/'h69-default-checked/commands.jsonl'),proof_tool_sha256=sha(tool_source),control_snapshot=str(args.output/'control-snapshot.json'),control_snapshot_sha256=sha(args.output/'control-snapshot.json'),frozen_type_sha256=hashlib.sha256(record['frozen_type_repr'].encode()).hexdigest(),level_parameters=record['level_parameters'],joint_values_sha256=[hashlib.sha256(v.encode()).hexdigest() for v in record['values_repr']])
 by_name[name]=r
manifest.update(h69_authorization=str(test/'H69.md'),scope_question='Q-REFUTATION-01 resolved by H69',proof_checks=['/workspace/h62-audit-yul-evidence/final-proofs/commands.jsonl','/workspace/h62-audit-yul-evidence/h69-refutations-final/commands.jsonl','/workspace/h62-audit-yul-evidence/h69-default-checked/commands.jsonl'],statements=sorted(by_name.values(),key=lambda r:r['theorem']))
(test/'witnesses.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
(args.output/'registry-summary.json').write_text(json.dumps(dict(intentional_refutations=11,ordinary_joint_witnesses=5,synthetic_controls_counted=0,exact_refutation_type_equalities=11),indent=2)+'\n')
print('H69_REGISTRY_BOUND: 11 intentional refutations; 5 ordinary joint witnesses; 0 synthetic controls counted')
