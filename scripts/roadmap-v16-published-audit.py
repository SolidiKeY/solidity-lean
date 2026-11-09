#!/usr/bin/env python3
"""Checked source ABI/dispatch consumers; no G48-G51 coverage closure."""
import sys,pathlib,json,copy,importlib.util,subprocess,unittest
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[1]
s=importlib.util.spec_from_file_location('heap',ROOT/'scripts/roadmap-v16-heap-audit.py')
h=importlib.util.module_from_spec(s);s.loader.exec_module(h)
core=h.core
PUB='099bfbe185731c354b12a40f28ccf5d98534c779'
PRE='Solidity.Roadmap.V16.'
PROPS={'dispatch_selected_stmt': ['before', 'hit'], 'dispatch_selected_run': ['before', 'hit'], 'dispatch_none_run': ['miss'], 'dispatch_guard_error': ['error'], 'dispatch_box_iff': ['before', 'hit'], 'dispatch_diamond_iff': ['before', 'hit'], 'dispatch_finite_diamond': ['before', 'hit', 'path', 'input', 'body'], 'abi_eager_observation': ['size', 'decoded', 'observed'], 'abi_certified_revert': ['revert'], 'abi_run_prerequisites': ['accepted'], 'abi_uint_finite_diamond': ['path', 'size', 'decoded', 'input', 'body']}
REQUIRED=[
 "Solidity.Roadmap.V16.PublishedControls.dispatch.body_box",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.body_diamond",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.body_positive",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.body_source",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.duplicate_guard",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.duplicate_true",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.fail_input",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.fail_path",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.fail_source",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.first_failure",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guard_error",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guard_failure",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guard_input",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guard_not_hit",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guard_path",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guard_source",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.hit",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.input",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_diamond",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_drop",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_frame_refused",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_hit",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_input",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_ordered",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_path",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_positive",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_source",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_source_observed",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_target_observed",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.no_candidate",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.no_late_failure",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.none_input",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.none_path",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.none_source",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.ordered",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.path",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.represented",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.selected_box",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.source_observed",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.target_observed",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.wrong_before",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.wrong_result",
 "Solidity.Roadmap.V16.PublishedControls.entry.accepted",
 "Solidity.Roadmap.V16.PublishedControls.entry.actual_entry_revert",
 "Solidity.Roadmap.V16.PublishedControls.entry.actual_number",
 "Solidity.Roadmap.V16.PublishedControls.entry.body",
 "Solidity.Roadmap.V16.PublishedControls.entry.decoded",
 "Solidity.Roadmap.V16.PublishedControls.entry.exhausted_decoder",
 "Solidity.Roadmap.V16.PublishedControls.entry.input",
 "Solidity.Roadmap.V16.PublishedControls.entry.late_blocked",
 "Solidity.Roadmap.V16.PublishedControls.entry.late_entry",
 "Solidity.Roadmap.V16.PublishedControls.entry.lazy_reference",
 "Solidity.Roadmap.V16.PublishedControls.entry.ordered",
 "Solidity.Roadmap.V16.PublishedControls.entry.output_post",
 "Solidity.Roadmap.V16.PublishedControls.entry.packet_published_data",
 "Solidity.Roadmap.V16.PublishedControls.entry.packet_published_free",
 "Solidity.Roadmap.V16.PublishedControls.entry.panic_blocked",
 "Solidity.Roadmap.V16.PublishedControls.entry.panic_entry",
 "Solidity.Roadmap.V16.PublishedControls.entry.path",
 "Solidity.Roadmap.V16.PublishedControls.entry.positive",
 "Solidity.Roadmap.V16.PublishedControls.entry.prerequisites",
 "Solidity.Roadmap.V16.PublishedControls.entry.represented",
 "Solidity.Roadmap.V16.PublishedControls.entry.size",
 "Solidity.Roadmap.V16.PublishedControls.entry.source",
 "Solidity.Roadmap.V16.PublishedControls.entry.source_observed",
 "Solidity.Roadmap.V16.PublishedControls.entry.state_binding",
 "Solidity.Roadmap.V16.PublishedControls.entry.target_observed",
 "Solidity.Roadmap.V16.PublishedControls.entry.wrong_binding",
 "Solidity.Roadmap.V16.PublishedControls.entry.wrong_compiler_result",
 "Solidity.Roadmap.V16.PublishedControls.entry.wrong_decode",
 "Solidity.Roadmap.V16.PublishedControls.entry.wrong_input_binding",
 "Solidity.Roadmap.V16.PublishedControls.entry.wrong_kind_reverts"
]
AUXILIARY=[
 "Solidity.Roadmap.V16.PublishedControls.dispatch.absent._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.all_miss._proof_1_3",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.all_miss._proof_1_4",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.all_miss._simp_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.all_miss._simp_1_2",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.badGuard._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.before._proof_1_2",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.before._simp_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.bodyOut.eq_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.body_box._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.body_diamond._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.body_positive._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.chosen._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.compiled._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.duplicate_true._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.failCompiled._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.failP.eq_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.fail_input._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.fail_input._proof_1_2",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.fail_path._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.fail_source._proof_1_2",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guard._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guard._proof_2",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guard._proof_3",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guardCompiled._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guard_error._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guard_input._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guard_input._proof_1_2",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.guard_path._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.hit._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.input._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.input._proof_1_2",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.localCompiled._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.localOut.eq_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.localPost._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_diamond._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_frame_refused._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_hit._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_input._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_input._proof_1_2",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_path._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_positive._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_source_observed._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.local_target_observed._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.machine._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.miss._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.noneCompiled._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.none_input._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.none_input._proof_1_2",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.none_path._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.observeSource._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.path._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.post._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.source_observed._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.dispatch.target_observed._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.P.eq_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.actual_number._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.compiled.eq_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.input._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.input._proof_1_2",
 "Solidity.Roadmap.V16.PublishedControls.entry.output.eq_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.output_post._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.output_post._proof_1_2",
 "Solidity.Roadmap.V16.PublishedControls.entry.packet_published_data._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.path._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.positive._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.post._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.post._proof_2",
 "Solidity.Roadmap.V16.PublishedControls.entry.size._proof_1_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.value._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.value._proof_2",
 "Solidity.Roadmap.V16.PublishedControls.entry.wrongValue._proof_1",
 "Solidity.Roadmap.V16.PublishedControls.entry.wrongValue._proof_2",
 "Solidity.Roadmap.V16.PublishedControls.instDecidableEqTResDenoteBool_tests._proof_6"
]
BASELINE_IDS_SHA256='219f0f3d3e7c09660fa57df20454ffd2c5050b613cbabb5f749bf82d69f089da'
NAMES={PRE+n for n in PROPS}
LINKS={'dispatch.represented':'dispatch_finite_diamond','dispatch.selected_box':'dispatch_box_iff','dispatch.guard_source':'dispatch_guard_error','entry.represented':'abi_uint_finite_diamond','entry.actual_entry_revert':'abi_certified_revert','entry.prerequisites':'abi_run_prerequisites'}
def statements(rows,policy):
 core.require(policy['revision']==PUB,'wrong published revision')
 core.require(set(policy['theorems'])==NAMES,'absent/extra theorem')
 core.require(set(policy['axiomPins'])==NAMES|set(REQUIRED)|set(AUXILIARY),'missing or extra exact scoped axiom pin')
 for name in NAMES:
  core.require(name in rows,'absent actual theorem')
  row=rows[name]
  core.require(h.contract(row)==policy['theorems'][name],'altered complete statement or premise telescope')
  core.require([p['name'] for p in row['premises'] if p['isProp']]==PROPS[name.removeprefix(PRE)],'premise-only desired execution or notExhausted assumption')
  core.require(set(row['axioms'])<=core.AXIOMS,'unapproved headline axiom')
  core.require(sorted(row['axioms'])==policy['axiomPins'][name],'actual headline axiom set drifted')
  core.require(not any('PublicCorrectness' in n for n in row['typeConstants']),'assumed desired simulation')
def controls(nodes,policy):
 core.require(set(policy['controls'])==set(REQUIRED),'absent required control')
 for name in REQUIRED:
  core.require(name in nodes,'missing actual control')
  row=nodes[name]
  core.require(h.contract(row)==policy['controls'][name],'changed control conclusion/premises')
  core.require(not row['premises'],'generic or premise-only alleged closed semantic control')
 core.require(set(policy['auxiliaryContracts'])==set(AUXILIARY),'absent auxiliary contract')
 for name in AUXILIARY:
  core.require(name in nodes and h.contract(nodes[name])==policy['auxiliaryContracts'][name],'changed generated helper contract; not a semantic witness')
 for name,dep in LINKS.items():
  core.require(PRE+dep in nodes[PRE+'PublishedControls.'+name]['dependencies'],'absent NEW consumer application')
 for family in ['dispatch','entry']:
  reached=h.closure(nodes,[PRE+'PublishedControls.'+family+'.compiled'])
  deps={d for n in reached for d in nodes[n].get('dependencies',[])}
  origin='Solidity.Evm.Compiler.compile' if family=='dispatch' else '_private.Solidity.Evm.MemoryAllocSourceExamples.0.Solidity.Evm.Memory.AllocSourceExamples.compiled'
  core.require(origin in deps,'not actual public compiler or published canonical output')
 for name in set(REQUIRED)|set(AUXILIARY):
  core.require(sorted(nodes[name]['axioms'])==policy['axiomPins'][name],'actual control/auxiliary axiom set drifted')
 return h.closure(nodes,set(REQUIRED)|set(AUXILIARY)|NAMES)
def global_report(data):
 h.global_report(data)
 # Imported ABI/dispatch constructor accounting extends, never drops, the old set.
 required={'constructor:Solidity.DispatchArm.mk','constructor:Solidity.AbiEntry.Val.word'}
 core.require(required <= {r['id'] for r in data['report']['obligations']},'new actual constructor omitted')
 baseline=POLICY['baselineObligationIds']
 core.require(core.digest(json.dumps(baseline,separators=(',',':')).encode())==BASELINE_IDS_SHA256,'wrong frozen inherited obligation IDs')
 core.require(set(baseline)<={r['id'] for r in data['report']['obligations']},'dropped inherited obligation')
class CorruptionControls(unittest.TestCase):
 def test_live(self):statements(ROWS,POLICY);controls(NODES,POLICY);global_report(DATA)
 def test_wrong_revision(self):
  p=copy.deepcopy(POLICY);p['revision']='0'*40
  with self.assertRaises(core.Invalid):statements(ROWS,p)
 def test_absent_theorem(self):
  n=copy.deepcopy(ROWS);n.pop(PRE+'abi_uint_finite_diamond')
  with self.assertRaises(core.Invalid):statements(n,POLICY)
 def test_wrong_conclusion(self):
  n=copy.deepcopy(ROWS);n[PRE+'dispatch_finite_diamond']['type']='True'
  with self.assertRaises(core.Invalid):statements(n,POLICY)
 def test_source_success_premise(self):
  n=copy.deepcopy(ROWS);n[PRE+'abi_uint_finite_diamond']['premises'].append(dict(name='desiredSource',isProp=True))
  with self.assertRaises(core.Invalid):statements(n,POLICY)
 def test_not_exhausted_premise(self):
  n=copy.deepcopy(ROWS);n[PRE+'dispatch_finite_diamond']['premises'].append(dict(name='notExhausted',isProp=True))
  with self.assertRaises(core.Invalid):statements(n,POLICY)
 def test_strengthened_input(self):
  n=copy.deepcopy(ROWS);next(p for p in n[PRE+'abi_uint_finite_diamond']['premises'] if p['name']=='input')['closedExpr']+=' oracle'
  with self.assertRaises(core.Invalid):statements(n,POLICY)
 def test_erased_drop_or_payload(self):
  n=copy.deepcopy(ROWS);n[PRE+'dispatch_guard_error']['type']='failure'
  with self.assertRaises(core.Invalid):statements(n,POLICY)
 def test_allowed_but_changed_axiom_pin(self):
  n=copy.deepcopy(ROWS);n[PRE+'abi_certified_revert']['axioms'].append('Classical.choice')
  with self.assertRaises(core.Invalid):statements(n,POLICY)
 def test_unapproved_axiom(self):
  n=copy.deepcopy(ROWS);n[PRE+'abi_eager_observation']['axioms'].append('sorryAx')
  with self.assertRaises(core.Invalid):statements(n,POLICY)
 def test_absent_control(self):
  p=copy.deepcopy(POLICY);p['controls'].pop(REQUIRED[0])
  with self.assertRaises(core.Invalid):controls(NODES,p)
 def test_premise_only_control(self):
  n=copy.deepcopy(NODES);n[REQUIRED[0]]['premises'].append(dict(name='oracle',isProp=True))
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_polymorphic_auxiliary_is_not_witness(self):
  n=copy.deepcopy(NODES);n[REQUIRED[0]]['premises'].append(dict(name='alpha',isProp=False,type='Type'))
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_absent_helper_contract(self):
  p=copy.deepcopy(POLICY);p['auxiliaryContracts'].pop(AUXILIARY[0])
  with self.assertRaises(core.Invalid):controls(NODES,p)
 def test_wrong_compiler_origin(self):
  n=copy.deepcopy(NODES);n[PRE+'PublishedControls.dispatch.compiled']['dependencies']=[]
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_missing_consumer_application(self):
  n=copy.deepcopy(NODES);n[PRE+'PublishedControls.entry.represented']['dependencies']=[]
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_hidden_oracle(self):
  n=copy.deepcopy(NODES);n[PRE+'PublishedControls.entry.compiled']['dependencies'].append('Solidity.Roadmap.PublicCorrectness')
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_missing_private_helper(self):
  n=copy.deepcopy(NODES);d=next(d for d in n[PRE+'abi_uint_finite_diamond']['dependencies'] if h.owned(d));n.pop(d)
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_missing_global_obligation(self):
  d=copy.deepcopy(DATA);d['report']['obligations'].pop()
  with self.assertRaises(core.Invalid):global_report(d)
 def test_false_coverage(self):
  d=copy.deepcopy(DATA);d['report']['obligations'][0]['status']='closed'
  with self.assertRaises(core.Invalid):global_report(d)
 def test_false_lane_completion(self):
  d=copy.deepcopy(DATA);d['report']['laneComplete']=True
  with self.assertRaises(core.Invalid):global_report(d)
if __name__=='__main__':
 POLICY=json.loads((ROOT/'tests/roadmap-v16/published-premises.json').read_text())
 DATA=json.loads(pathlib.Path(sys.argv[1]).read_text());global_report(DATA)
 METAS=[core.snapshot(pathlib.Path(sys.argv[2]))]
 NODES=h.merged(METAS);ROWS={r['name']:r for r in DATA['inventory']['theorems']}
 POLICY=json.loads((ROOT/'tests/roadmap-v16/published-premises.json').read_text())
 statements(ROWS,POLICY);reached=controls(NODES,POLICY)
 for ref in ['HEAD','origin/master']:subprocess.run(['git','merge-base','--is-ancestor',PUB,ref],cwd=ROOT,check=True)
 paths=['Solidity/Semantics/'+f+'.lean' for f in ['AbiEntry','AbiEntryProofs','AbiEntryChecks','Dispatch']]+['Solidity/Evm/'+f+'.lean' for f in ['Compiler','MemoryCompileExamples','MemoryAllocSourceExamples']]
 paths+=['Solidity/Syntax/DispatchChain.lean']
 hashes={}
 for path in paths:
  pub=subprocess.check_output(['git','show',PUB+':'+path],cwd=ROOT)
  core.require((ROOT/path).read_bytes()==pub,'modified published producer')
  hashes[path]=core.digest(pub)
 pathlib.Path(sys.argv[3]).write_text(json.dumps(dict(head=DATA['inventory']['head'],revision=PUB,producerHashes=hashes,headlineTheorems=sorted(NAMES),closedScopedControls=REQUIRED,generatedAuxiliaryContracts=AUXILIARY,scopedClosure=reached,actualAxioms={n:ROWS[n]['axioms'] for n in sorted(NAMES)},policySha256=core.digest((ROOT/'tests/roadmap-v16/published-premises.json').read_bytes()),auditScriptSha256=core.digest(pathlib.Path(__file__).read_bytes()),allGlobalObligations='OPEN',laneComplete=False,sourceElaboratorCorrespondence=False,externalByteEvm=False,boundary='Source decoder and existing intrinsic dispatch only; compiler Input constructed in controls, retained in consumers; no V13 packet bridge or Source admission'),indent=2)+'\n')
 unittest.main(argv=[sys.argv[0]],verbosity=2)
