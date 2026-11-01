#!/usr/bin/env python3
"""Actual canonical mixed compiler/source-spec accounting; full coverage OPEN."""
import sys,pathlib,json,copy,importlib.util,subprocess,unittest
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[1]
sp=importlib.util.spec_from_file_location('heap',ROOT/'scripts/roadmap-v16-heap-audit.py')
h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h);core=h.core
PUB='099bfbe185731c354b12a40f28ccf5d98534c779'
PRE='Solidity.Roadmap.V16.'
PROPS={'finite_memory_reconstruct': ['path'], 'finite_memory_compile_inversion': ['path', 'accepted'], 'finite_memory_compile_append': ['compiledHead', 'compiledTail'], 'finite_memory_compile_append_link': ['link', 'compiledHead', 'compiledTail'], 'finite_memory_certificate_code': ['path'], 'finite_memory_certificate_fragment': ['path'], 'finite_memory_public_append_code': ['wholePath', 'headPath', 'tailPath', 'link', 'source', 'compiledWhole', 'compiledHead', 'compiledTail'], 'intrinsic_append_run': [], 'intrinsic_append_box_iff': [], 'intrinsic_append_diamond_iff': []}
REQUIRED=[
 "Solidity.Roadmap.V16.MixedMemoryControls.code_composes",
 "Solidity.Roadmap.V16.MixedMemoryControls.diamond",
 "Solidity.Roadmap.V16.MixedMemoryControls.exact_allocator",
 "Solidity.Roadmap.V16.MixedMemoryControls.false_nested_diamond",
 "Solidity.Roadmap.V16.MixedMemoryControls.halts.exhaustion_append",
 "Solidity.Roadmap.V16.MixedMemoryControls.halts.exhaustion_diamond",
 "Solidity.Roadmap.V16.MixedMemoryControls.halts.exhaustion_refused",
 "Solidity.Roadmap.V16.MixedMemoryControls.halts.exhaustion_source",
 "Solidity.Roadmap.V16.MixedMemoryControls.halts.payload_append",
 "Solidity.Roadmap.V16.MixedMemoryControls.halts.payload_source",
 "Solidity.Roadmap.V16.MixedMemoryControls.halts.wrong_payload",
 "Solidity.Roadmap.V16.MixedMemoryControls.initial_allocator",
 "Solidity.Roadmap.V16.MixedMemoryControls.initial_repr",
 "Solidity.Roadmap.V16.MixedMemoryControls.low_prefix_code",
 "Solidity.Roadmap.V16.MixedMemoryControls.low_prefix_fragment",
 "Solidity.Roadmap.V16.MixedMemoryControls.nested_box",
 "Solidity.Roadmap.V16.MixedMemoryControls.nested_diamond",
 "Solidity.Roadmap.V16.MixedMemoryControls.ordered",
 "Solidity.Roadmap.V16.MixedMemoryControls.output_post",
 "Solidity.Roadmap.V16.MixedMemoryControls.prefix_accepted",
 "Solidity.Roadmap.V16.MixedMemoryControls.prefix_core",
 "Solidity.Roadmap.V16.MixedMemoryControls.prefix_diamond",
 "Solidity.Roadmap.V16.MixedMemoryControls.prefix_input",
 "Solidity.Roadmap.V16.MixedMemoryControls.prefix_low_accepted",
 "Solidity.Roadmap.V16.MixedMemoryControls.prefix_representation",
 "Solidity.Roadmap.V16.MixedMemoryControls.prefix_source",
 "Solidity.Roadmap.V16.MixedMemoryControls.prefix_target",
 "Solidity.Roadmap.V16.MixedMemoryControls.profileGap.assertion_allocation_refused",
 "Solidity.Roadmap.V16.MixedMemoryControls.profileGap.assertion_allocation_source_success",
 "Solidity.Roadmap.V16.MixedMemoryControls.profileGap.assertion_prefix_accepted",
 "Solidity.Roadmap.V16.MixedMemoryControls.reached_allocator",
 "Solidity.Roadmap.V16.MixedMemoryControls.reached_repr",
 "Solidity.Roadmap.V16.MixedMemoryControls.represented",
 "Solidity.Roadmap.V16.MixedMemoryControls.source_observed",
 "Solidity.Roadmap.V16.MixedMemoryControls.source_sequence",
 "Solidity.Roadmap.V16.MixedMemoryControls.staged",
 "Solidity.Roadmap.V16.MixedMemoryControls.stale_budget_not_capacity",
 "Solidity.Roadmap.V16.MixedMemoryControls.stale_initial_cost",
 "Solidity.Roadmap.V16.MixedMemoryControls.suffix_accepted",
 "Solidity.Roadmap.V16.MixedMemoryControls.suffix_cost",
 "Solidity.Roadmap.V16.MixedMemoryControls.suffix_diamond",
 "Solidity.Roadmap.V16.MixedMemoryControls.suffix_input",
 "Solidity.Roadmap.V16.MixedMemoryControls.suffix_memory",
 "Solidity.Roadmap.V16.MixedMemoryControls.suffix_source",
 "Solidity.Roadmap.V16.MixedMemoryControls.target_observed",
 "Solidity.Roadmap.V16.MixedMemoryControls.whole_accepted",
 "Solidity.Roadmap.V16.MixedMemoryControls.whole_cost",
 "Solidity.Roadmap.V16.MixedMemoryControls.whole_input",
 "Solidity.Roadmap.V16.MixedMemoryControls.whole_memory",
 "Solidity.Roadmap.V16.MixedMemoryControls.whole_positive",
 "Solidity.Roadmap.V16.MixedMemoryControls.whole_source",
 "Solidity.Roadmap.V16.MixedMemoryControls.wrong_alias",
 "Solidity.Roadmap.V16.MixedMemoryControls.wrong_cursor",
 "Solidity.Roadmap.V16.MixedMemoryControls.wrong_failure",
 "Solidity.Roadmap.V16.MixedMemoryControls.wrong_frame",
 "Solidity.Roadmap.V16.MixedMemoryControls.wrong_reached_input",
 "Solidity.Roadmap.V16.MixedMemoryControls.wrong_source_length",
 "Solidity.Roadmap.V16.MixedMemoryControls.wrong_stale_cost"
]
NEGATIVE=['Solidity.Roadmap.V16.MixedMemoryControls.halts.exhaustion_no_success']
BASELINE_SHA='2ce75209221bd542de269fc1affe6abed90533a6a545136ca9d54613a92b7179'

NAMES={PRE+n for n in PROPS}
LINKS={'code_composes':['finite_memory_compile_append_link','finite_memory_compile_inversion'],
 'source_sequence':['intrinsic_append_run'],'staged':['MixedMemoryControls.code_composes','MixedMemoryControls.source_sequence','compiler_nonpaying_diamond'],
 'nested_box':['intrinsic_append_box_iff'],'nested_diamond':['intrinsic_append_diamond_iff'],
 'false_nested_diamond':['intrinsic_append_diamond_iff','finite_heap_diamond'],
 'halts.payload_append':['intrinsic_append_run'],'halts.exhaustion_append':['intrinsic_append_run'],
 'halts.exhaustion_diamond':['intrinsic_append_diamond_iff']}
def statements(rows,p):
 core.require(p['revision']==PUB,'wrong published revision')
 core.require(set(p['theorems'])==NAMES,'absent headline')
 for name in NAMES:
  core.require(name in rows,'absent actual theorem')
  row=rows[name]
  core.require(h.contract(row)==p['theorems'][name],'altered exact statement or dependent premise')
  core.require([a['name'] for a in row['premises'] if a['isProp']]==PROPS[name.removeprefix(PRE)],'desired simulation/target/source/notExhausted premise')
  core.require(set(row['axioms'])<=core.AXIOMS,'unapproved axiom')
def controls(nodes,p):
 core.require(set(p['controls'])==set(REQUIRED),'missing concrete combination/control')
 for name in REQUIRED:
  core.require(name in nodes,'missing actual closed control')
  core.require(h.contract(nodes[name])==p['controls'][name] and not nodes[name]['premises'],'changed/premise-only/polymorphic alleged closed witness')
 core.require(set(p['negativeLaws'])==set(NEGATIVE),'missing actual universal rejection law')
 for name in NEGATIVE:
  core.require(name in nodes and h.contract(nodes[name])==p['negativeLaws'][name],'altered bounded-output rejection')
  core.require([a['name'] for a in nodes[name]['premises']]==['o'] and not nodes[name]['premises'][0]['isProp'],'rejection law adds an assumption')
 for name,deps in LINKS.items():
  reached=h.closure(nodes,[PRE+'MixedMemoryControls.'+name]);actual={d for n in reached for d in nodes[n]['dependencies']}
  for dep in deps:core.require(PRE+dep in actual,'missing NEW composition/spec consumer application')
 for field in ['prefixCompiled','compiled']:
  core.require('Solidity.Evm.Compiler.compile' in nodes[PRE+'MixedMemoryControls.'+field]['dependencies'],'not actual canonical public compilation')
 core.require('_private.Solidity.Evm.MemoryAllocSourceExamples.0.Solidity.Evm.Memory.AllocSourceExamples.compiled' in nodes[PRE+'MixedMemoryControls.suffixCompiled']['dependencies'],'not published canonical suffix')
 reached=h.closure(nodes,set(REQUIRED)|set(NEGATIVE)|NAMES)
 core.require(set(p['axiomPins'])==set(reached) and set(p['dependencyPins'])==set(reached),'missing reached helper/dependency/axiom pin')
 for name in reached:
  core.require(sorted(nodes[name]['axioms'])==p['axiomPins'][name],'actual scoped axiom drift')
  core.require(sorted(set(nodes[name]['dependencies']))==p['dependencyPins'][name],'actual scoped dependency drift')
 return reached

def global_report(d,p):
 h.global_report(d)
 baseline=p['baselineObligationIds'];core.require(core.digest(json.dumps(baseline,separators=(',',':')).encode())==BASELINE_SHA,'changed inherited obligation IDs')
 core.require(set(baseline)<={x['id'] for x in d['report']['obligations']},'dropped inherited obligation')
 core.require(next(x for x in d['report']['obligations'] if x['id']=='combination:17')['status']=='open','scoped example falsely closes mixed profile')

class CorruptionControls(unittest.TestCase):
 def test_live(self):statements(ROWS,POLICY);controls(NODES,POLICY);global_report(DATA,POLICY)
 def test_wrong_revision(self):
  p=copy.deepcopy(POLICY);p['revision']='0'*40
  with self.assertRaises(core.Invalid):statements(ROWS,p)
 def test_absent_theorem(self):
  n=copy.deepcopy(ROWS);n.pop(PRE+'intrinsic_append_run')
  with self.assertRaises(core.Invalid):statements(n,POLICY)
 def test_erased_halt_or_payload(self):
  n=copy.deepcopy(ROWS);n[PRE+'intrinsic_append_run']['type']='success only'
  with self.assertRaises(core.Invalid):statements(n,POLICY)
 def test_source_success_assumption(self):
  n=copy.deepcopy(ROWS);n[PRE+'finite_memory_compile_append']['premises'].append(dict(name='desiredSource',isProp=True))
  with self.assertRaises(core.Invalid):statements(n,POLICY)
 def test_not_exhausted_assumption(self):
  n=copy.deepcopy(ROWS);n[PRE+'intrinsic_append_diamond_iff']['premises'].append(dict(name='notExhausted',isProp=True))
  with self.assertRaises(core.Invalid):statements(n,POLICY)
 def test_strengthened_compiler_equation(self):
  n=copy.deepcopy(ROWS);next(a for a in n[PRE+'finite_memory_compile_append']['premises'] if a['name']=='compiledHead')['closedExpr']+=' oracle'
  with self.assertRaises(core.Invalid):statements(n,POLICY)
 def test_absent_control(self):
  p=copy.deepcopy(POLICY);p['controls'].pop(REQUIRED[0])
  with self.assertRaises(core.Invalid):controls(NODES,p)
 def test_assumed_reached_input(self):
  n=copy.deepcopy(NODES);n[PRE+'MixedMemoryControls.staged']['premises'].append(dict(name='desiredInput',isProp=True))
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_polymorphic_closed_control(self):
  n=copy.deepcopy(NODES);n[REQUIRED[0]]['premises'].append(dict(name='alpha',isProp=False))
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_erased_stack_or_rep(self):
  n=copy.deepcopy(NODES);n[PRE+'MixedMemoryControls.staged']['type']='True'
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_wrong_prefix_compiler(self):
  n=copy.deepcopy(NODES);n[PRE+'MixedMemoryControls.prefixCompiled']['dependencies']=[]
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_wrong_published_suffix(self):
  n=copy.deepcopy(NODES);n[PRE+'MixedMemoryControls.suffixCompiled']['dependencies']=[]
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_unapproved_axiom(self):
  n=copy.deepcopy(NODES);n[PRE+'MixedMemoryControls.code_composes']['axioms'].append('sorryAx')
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_allowed_axiom_drift(self):
  p=copy.deepcopy(POLICY);p['axiomPins'][PRE+'MixedMemoryControls.code_composes']=[]
  with self.assertRaises(core.Invalid):controls(NODES,p)
 def test_missing_private_helper(self):
  n=copy.deepcopy(NODES);key=next(d for d in POLICY['dependencyPins'] if d.startswith('_private.Solidity.Roadmap.V16.'));n.pop(key)
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_missing_dependency_pin(self):
  p=copy.deepcopy(POLICY);p['dependencyPins'].pop(next(iter(p['dependencyPins'])))
  with self.assertRaises(core.Invalid):controls(NODES,p)
 def test_hidden_desired_simulation(self):
  n=copy.deepcopy(NODES);n[PRE+'MixedMemoryControls.lowPrefix']['dependencies'].append('Solidity.Roadmap.PublicCorrectness')
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_false_coverage_closure(self):
  d=copy.deepcopy(DATA);next(x for x in d['report']['obligations'] if x['id']=='combination:17')['status']='closed'
  with self.assertRaises(core.Invalid):global_report(d,POLICY)
 def test_dropped_old_obligation(self):
  d=copy.deepcopy(DATA);d['report']['obligations'].pop()
  with self.assertRaises(core.Invalid):global_report(d,POLICY)
 def test_false_lane_complete(self):
  d=copy.deepcopy(DATA);d['report']['laneComplete']=True
  with self.assertRaises(core.Invalid):global_report(d,POLICY)

if __name__=='__main__':
 DATA=json.loads(pathlib.Path(sys.argv[1]).read_text());POLICY=json.loads((ROOT/'tests/roadmap-v16/mixed-premises.json').read_text());global_report(DATA,POLICY)
 meta=core.snapshot(pathlib.Path(sys.argv[2]));NODES=h.merged([meta]);ROWS={x['name']:x for x in DATA['inventory']['theorems']}
 statements(ROWS,POLICY);reached=controls(NODES,POLICY)
 for ref in ['HEAD','origin/master']:subprocess.run(['git','merge-base','--is-ancestor',PUB,ref],cwd=ROOT,check=True)
 paths=['Solidity/Evm/'+f+'.lean' for f in ['Compiler','MemoryCompile','MemoryGrowResult','MemorySource','MemoryStructAlloc','MemoryAllocSourceExamples','MemoryCompileExamples']]+['Solidity/Semantics/Run.lean','Solidity/Calculus/Correct.lean']
 hashes={}
 for path in paths:
  pub=subprocess.check_output(['git','show',PUB+':'+path],cwd=ROOT);core.require((ROOT/path).read_bytes()==pub,'published producer changed');hashes[path]=core.digest(pub)
 pathlib.Path(sys.argv[3]).write_text(json.dumps(dict(head=DATA['inventory']['head'],revision=PUB,producerHashes=hashes,headlineTheorems=sorted(NAMES),closedControlStatements=REQUIRED,boundedNegativeOutputLaws=NEGATIVE,scopedClosure=reached,actualAxiomPins=POLICY['axiomPins'],actualDependencyPins=POLICY['dependencyPins'],policySha256=core.digest((ROOT/'tests/roadmap-v16/mixed-premises.json').read_bytes()),auditScriptSha256=core.digest(pathlib.Path(__file__).read_bytes()),allGlobalObligations='OPEN',laneComplete=False,fullMixedProfileCompatibility=False,externalByteEvm=False,boundary='Actual canonical scalar prefix and published allocator suffix; real Inputs and all3publicRep. Initial emptyheap BaseExtends vacuous; nearEnd arithmetic only; exact source halt/spec laws preserve exhausted diamond. No V12 frame/SourceSpec/wholeG03combo17 closure.'),indent=2)+'\n')
 unittest.main(argv=[sys.argv[0]],verbosity=2)
