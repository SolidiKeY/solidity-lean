#!/usr/bin/env python3
"""Scoped actual finite/core theorem accounting. Never closes G48-G51 coverage."""
import pathlib,sys,json,copy,hashlib,subprocess,importlib.util,unittest
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('core',ROOT/'scripts/roadmap-v16-accounting.py')
core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
PUB='5f6a75b6038371a3917dbe08b660d5f2d1207c58'
PRE='Solidity.Roadmap.V16.'
PROPS={'finite_heap_result': ['path', 'input'],
 'finite_heap_not_exhausted': ['path', 'input'],
 'finite_heap_diamond': ['path', 'input', 'diamond'],
 'finite_heap_box': ['path', 'input', 'box'],
 'finite_heap_failure': ['path', 'input', 'source'],
 'finite_heap_diamond_iff': ['path', 'input'],
 'finite_heap_box_iff': ['path', 'input'],
 'finite_memory_cost': ['path'],
 'finite_memory_rep_iff': ['path'],
 'compiler_not_exhausted': ['input'],
 'compiler_diamond': ['input', 'diamond'],
 'compiler_box_target': ['input', 'box', 'target'],
 'compiler_nonpaying_diamond': ['input', 'nonpaying', 'diamond'],
 'compiler_source_error': ['input', 'source']}
REQUIRED=['Solidity.Roadmap.V16.FiniteHeapControls.objects.input',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.path',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.diamond',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.represented',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.ordered',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.wrong_output',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.wrong_alias',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.wrong_frame',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.wrong_pointer',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.bad_path',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.bad_input',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.bad_source',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.exact_failure',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.false_box',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.box_failure',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.no_diamond',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.no_wrong_payload',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.wrong_spec',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.input',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.path',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.diamond',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.represented',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.ordered',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.wrong_output',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.wrong_alias',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.wrong_frame',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.wrong_pointer',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.bad_path',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.bad_input',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.bad_source',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.exact_failure',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.false_box',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.box_failure',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.no_diamond',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.no_wrong_payload',
 'Solidity.Roadmap.V16.FiniteHeapControls.references.wrong_spec',
 'Solidity.Roadmap.V16.FiniteHeapControls.objects.allocator',
 'Solidity.Roadmap.V16.FiniteHeapControls.allocation.input',
 'Solidity.Roadmap.V16.FiniteHeapControls.allocation.cost',
 'Solidity.Roadmap.V16.FiniteHeapControls.allocation.source',
 'Solidity.Roadmap.V16.FiniteHeapControls.allocation.diamond',
 'Solidity.Roadmap.V16.FiniteHeapControls.allocation.ordered',
 'Solidity.Roadmap.V16.FiniteHeapControls.allocation.cursor20',
 'Solidity.Roadmap.V16.FiniteHeapControls.allocation.wrong_frame',
 'Solidity.Roadmap.V16.FiniteHeapControls.allocation.wrong_allocation_cursor',
 'Solidity.Roadmap.V16.FiniteHeapControls.allocation.protected_input',
 'Solidity.Roadmap.V16.FiniteHeapControls.allocation.protected_success',
 'Solidity.Roadmap.V16.FiniteHeapControls.badRhs.input',
 'Solidity.Roadmap.V16.FiniteHeapControls.badRhs.source',
 'Solidity.Roadmap.V16.FiniteHeapControls.badRhs.exact_failure',
 'Solidity.Roadmap.V16.FiniteHeapControls.badRhs.false_box',
 'Solidity.Roadmap.V16.FiniteHeapControls.badRhs.box_failure',
 'Solidity.Roadmap.V16.FiniteHeapControls.badRhs.no_diamond',
 'Solidity.Roadmap.V16.FiniteHeapControls.badRhs.no_wrong_payload',
 'Solidity.Roadmap.V16.FiniteHeapControls.badIndex.input',
 'Solidity.Roadmap.V16.FiniteHeapControls.badIndex.source',
 'Solidity.Roadmap.V16.FiniteHeapControls.badIndex.exact_failure',
 'Solidity.Roadmap.V16.FiniteHeapControls.badIndex.false_box',
 'Solidity.Roadmap.V16.FiniteHeapControls.badIndex.box_failure',
 'Solidity.Roadmap.V16.FiniteHeapControls.badIndex.no_diamond',
 'Solidity.Roadmap.V16.FiniteHeapControls.badIndex.no_wrong_payload',
 'Solidity.Roadmap.V16.CoreConsumerControls.input',
 'Solidity.Roadmap.V16.CoreConsumerControls.source',
 'Solidity.Roadmap.V16.CoreConsumerControls.diamond',
 'Solidity.Roadmap.V16.CoreConsumerControls.represented',
 'Solidity.Roadmap.V16.CoreConsumerControls.machine_value',
 'Solidity.Roadmap.V16.CoreConsumerControls.wrong_output',
 'Solidity.Roadmap.V16.CoreConsumerControls.box_target',
 'Solidity.Roadmap.V16.CoreConsumerControls.frame_zero_admitted',
 'Solidity.Roadmap.V16.CoreConsumerControls.wrong_layout',
 'Solidity.Roadmap.V16.CoreConsumerControls.panic.input',
 'Solidity.Roadmap.V16.CoreConsumerControls.panic.source',
 'Solidity.Roadmap.V16.CoreConsumerControls.panic.preserved',
 'Solidity.Roadmap.V16.CoreConsumerControls.panic.no_box',
 'Solidity.Roadmap.V16.CoreConsumerControls.panic.no_diamond',
 'Solidity.Roadmap.V16.CoreConsumerControls.payment.input',
 'Solidity.Roadmap.V16.CoreConsumerControls.payment.source',
 'Solidity.Roadmap.V16.CoreConsumerControls.payment.diamond',
 'Solidity.Roadmap.V16.CoreConsumerControls.payment.target_run',
 'Solidity.Roadmap.V16.CoreConsumerControls.payment.represented',
 'Solidity.Roadmap.V16.CoreConsumerControls.payment.balances_observed',
 'Solidity.Roadmap.V16.CoreConsumerControls.payment.refused_input',
 'Solidity.Roadmap.V16.CoreConsumerControls.payment.refused_source',
 'Solidity.Roadmap.V16.CoreConsumerControls.payment.refusal_preserved',
 'Solidity.Roadmap.V16.CoreConsumerControls.payment.refused_not_diamond',
 'Solidity.Roadmap.V16.CoreConsumerControls.payment.corrupt_input_refused',
 'Solidity.Roadmap.V16.CoreConsumerControls.payment.corrupt_target_reverts',
 'Solidity.Roadmap.V16.CoreConsumerControls.payment.mismatched_source_target',
 'Solidity.Roadmap.V16.CoreConsumerControls.divergence.accepted',
 'Solidity.Roadmap.V16.CoreConsumerControls.divergence.input',
 'Solidity.Roadmap.V16.CoreConsumerControls.divergence.source',
 'Solidity.Roadmap.V16.CoreConsumerControls.divergence.fault',
 'Solidity.Roadmap.V16.CoreConsumerControls.divergence.box_without_success',
 'Solidity.Roadmap.V16.CoreConsumerControls.divergence.no_diamond',
 'Solidity.Roadmap.V16.CoreConsumerControls.divergence.not_finite_path',
 'Solidity.Roadmap.V16.CoreConsumerControls.divergence.no_target_success',
 'Solidity.Roadmap.V16.CoreConsumerControls.exhausted.genuine_diamond_without_success',
 'Solidity.Roadmap.V16.CoreConsumerControls.exhausted.refused']
NAMES={PRE+n for n in PROPS}

def contract(row):
 return dict(type=row['type'],premises=row['premises'],typeConstants=sorted(row['typeConstants']))

def statements(rows,policy):
 core.require(policy['revision']==PUB,'wrong published source revision')
 core.require(set(policy['theorems'])==NAMES,'missing/extra scoped theorem')
 for name in NAMES:
  core.require(name in rows,'absent actual theorem')
  row=rows[name]
  core.require(contract(row)==policy['theorems'][name],'altered full statement, conclusion or dependent premise telescope')
  core.require([p['name'] for p in row['premises'] if p['isProp']]==PROPS[name.removeprefix(PRE)],'extra/missing premise or desired run assumption')
  core.require(not any('PublicCorrectness' in n for n in row['typeConstants']),'desired simulation premise')
  core.require(set(row['axioms'])<=core.AXIOMS,'unapproved headline axiom')

def merged(metas):
 nodes={}
 for meta in metas:
  for row in meta['theorems']+meta['definitions']:
   core.require(set(row['axioms'])<=core.AXIOMS,'unapproved actual control/value/helper axiom')
   if row['name'] in nodes:
    prior=nodes[row['name']]
    core.require(row['type']==prior['type'] and set(row['dependencies'])==set(prior['dependencies']) and set(row['axioms'])==set(prior['axioms']),'contradictory checked module metadata')
   nodes[row['name']]=row
 return nodes

def owned(name):
 return name.startswith(PRE) or (name.startswith('_private.') and ('.'+PRE in name or name.startswith('_private.Solidity.Roadmap.V16.')))

def closure(nodes,roots):
 seen=set();todo=list(roots)
 while todo:
  name=todo.pop()
  if name in seen:continue
  core.require(name in nodes,'absent scoped theorem/value/helper')
  seen.add(name);row=nodes[name]
  core.require(set(row['axioms'])<=core.AXIOMS,'unapproved reached axiom')
  deps=set(row.get('dependencies',[]))|set(row.get('typeConstants',[]))
  core.require(not any('PublicCorrectness' in n for n in deps),'hidden desired simulation oracle')
  for dep in deps:
   core.require(not owned(dep) or dep in nodes,'missing reached owned private/value helper')
   if dep in nodes:todo.append(dep)
 return sorted(seen)

def controls(nodes,policy):
 core.require(set(policy['controls'])==set(REQUIRED),'absent required constructor/feature/control combination')
 for name in REQUIRED:
  core.require(name in nodes,'absent actual inhabited/rejection control')
  row=nodes[name]
  core.require(contract(row)==policy['controls'][name],'altered actual control statement/premises')
  core.require(not any(p['isProp'] for p in row['premises']),'premise-only claimed witness')
 for family,module,ns in [('objects','MemoryObjectArrayExamples','ObjectArrayExamples'),('references','MemoryRefArrayExamples','RefArrayExamples'),('allocation','MemoryAllocSourceExamples','AllocSourceExamples')]:
  for field,producer in [('P','program'),('compiled','compiled')]:
   row=nodes[PRE+'FiniteHeapControls.'+family+'.'+field]
   core.require(any(n.startswith('_private.Solidity.Evm.'+module+'.') and n.endswith('.'+ns+'.'+producer) for n in row['dependencies']),'wrong actual source/canonical compiler fixture origin')
 for family,suffix in [('badRhs','checkedBadRhs'),('badIndex','checkedBadIndex')]:
  row=nodes[PRE+'FiniteHeapControls.'+family+'.compiled']
  core.require('Solidity.Evm.Memory.CompileExamples.'+suffix in row['dependencies'],'wrong populated primitive-failure certificate')
 core.require('Solidity.Evm.Memory.CompileExamples.checkedCore' in nodes[PRE+'CoreConsumerControls.compiled']['dependencies'],'wrong actual core compiler origin')
 for name,dep in [('FiniteHeapControls.objects.represented','finite_heap_diamond'),('FiniteHeapControls.references.represented','finite_heap_diamond'),('FiniteHeapControls.allocation.represented','finite_heap_diamond'),('FiniteHeapControls.badRhs.exact_failure','finite_heap_failure'),('FiniteHeapControls.badIndex.box_failure','finite_heap_box'),('CoreConsumerControls.represented','compiler_nonpaying_diamond'),('CoreConsumerControls.payment.represented','compiler_box_target'),('CoreConsumerControls.divergence.fault','compiler_source_error')]:
  core.require(PRE+dep in nodes[PRE+name]['dependencies'],'missing NEW actual consumer application')
 for name in ['CoreConsumerControls.payment.compiled','CoreConsumerControls.payment.refusedCompiled']:
  reached=closure(nodes,[PRE+name]);deps={d for n in reached for d in nodes[n].get('dependencies',[])}
  core.require('Solidity.Evm.Compiler.compile' in deps,'not actual public compilation')
 core.require('Solidity.Evm.Compiler.compile' in nodes[PRE+'CoreConsumerControls.divergence.accepted']['typeConstants'],'missing actual canonical spin compilation equation')
 return closure(nodes,set(REQUIRED)|NAMES)

def global_report(data):
 inv=data['inventory'];ledger=core.validate_inventory(inv)
 core.validate_report(data['report'],inv,ledger)
 for arm in ['core','memory','referenceArrays','objects','construction','memoryLoops','memoryLoopScopes','memoryCalls']:
  core.require(any(row['id']=='constructor:Solidity.Evm.Compiler.Compilation.'+arm and row['status']=='open' for row in data['report']['obligations']),'missing or falsely closed compiler arm')

class CorruptionControls(unittest.TestCase):
 def test_live(self): statements(ROWS,POLICY);controls(NODES,POLICY);global_report(DATA)
 def test_wrong_revision(self):
  p=copy.deepcopy(POLICY);p['revision']='0'*40
  with self.assertRaises(core.Invalid):statements(ROWS,p)
 def test_absent_theorem_policy(self):
  p=copy.deepcopy(POLICY);p['theorems'].pop(next(iter(NAMES)))
  with self.assertRaises(core.Invalid):statements(ROWS,p)
 def test_extra_source_success_premise(self):
  r=copy.deepcopy(ROWS);r[PRE+'compiler_diamond']['premises'].append(dict(name='desiredSource',isProp=True))
  with self.assertRaises(core.Invalid):statements(r,POLICY)
 def test_extra_not_exhausted_premise(self):
  r=copy.deepcopy(ROWS);r[PRE+'finite_heap_diamond']['premises'].append(dict(name='notExhausted',isProp=True))
  with self.assertRaises(core.Invalid):statements(r,POLICY)
 def test_same_name_strengthened_input(self):
  r=copy.deepcopy(ROWS);p=next(p for p in r[PRE+'compiler_diamond']['premises'] if p['name']=='input');p['closedExpr']+=' strengthened'
  with self.assertRaises(core.Invalid):statements(r,POLICY)
 def test_erased_payment_alternative(self):
  r=copy.deepcopy(ROWS);r[PRE+'compiler_diamond']['type']='source success implies unconditional target success'
  with self.assertRaises(core.Invalid):statements(r,POLICY)
 def test_erased_branch_representation(self):
  r=copy.deepcopy(ROWS);r[PRE+'finite_heap_result']['type']='True'
  with self.assertRaises(core.Invalid):statements(r,POLICY)
 def test_unapproved_headline_axiom(self):
  r=copy.deepcopy(ROWS);r[PRE+'compiler_diamond']['axioms'].append('sorryAx')
  with self.assertRaises(core.Invalid):statements(r,POLICY)
 def test_absent_combination(self):
  p=copy.deepcopy(POLICY);p['controls'].pop(REQUIRED[0])
  with self.assertRaises(core.Invalid):controls(NODES,p)
 def test_premise_only_control(self):
  n=copy.deepcopy(NODES);n[REQUIRED[0]]['premises'].append(dict(name='oracle',isProp=True))
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_wrong_public_fixture(self):
  n=copy.deepcopy(NODES);n[PRE+'FiniteHeapControls.objects.compiled']['dependencies']=[]
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_missing_actual_input_control(self):
  n=copy.deepcopy(NODES);n.pop(PRE+'CoreConsumerControls.payment.corrupt_input_refused')
  with self.assertRaises(core.Invalid):controls(n,POLICY)
 def test_hidden_oracle_value(self):
  n=copy.deepcopy(NODES);n[PRE+'FiniteHeapControls.objects.compiled']['dependencies'].append('Solidity.Roadmap.PublicCorrectness')
  with self.assertRaises(core.Invalid):closure(n,[PRE+'FiniteHeapControls.objects.compiled'])
 def test_missing_actual_owned_helper(self):
  n=copy.deepcopy(NODES);dep=next(d for d in n[PRE+'compiler_diamond']['dependencies'] if owned(d));n.pop(dep)
  with self.assertRaises(core.Invalid):closure(n,[PRE+'compiler_diamond'])
 def test_unapproved_value_axiom(self):
  n=copy.deepcopy(NODES);n[PRE+'FiniteHeapControls.objects.compiled']['axioms'].append('sorryAx')
  with self.assertRaises(core.Invalid):closure(n,[PRE+'FiniteHeapControls.objects.compiled'])
 def test_global_closure_claim(self):
  d=copy.deepcopy(DATA);d['report']['obligations'][0]['status']='closed'
  with self.assertRaises(core.Invalid):global_report(d)
 def test_absent_global_constructor_or_combination(self):
  d=copy.deepcopy(DATA);d['report']['obligations'].pop()
  with self.assertRaises(core.Invalid):global_report(d)
 def test_false_lane_completion(self):
  d=copy.deepcopy(DATA);d['report']['laneComplete']=True
  with self.assertRaises(core.Invalid):global_report(d)

if __name__=='__main__':
 DATA=json.loads(pathlib.Path(sys.argv[1]).read_text());global_report(DATA)
 METAS=[core.snapshot(pathlib.Path(p)) for p in sys.argv[2:4]]
 NODES=merged(METAS);ROWS={r['name']:r for r in DATA['inventory']['theorems']}
 POLICY=json.loads((ROOT/'tests/roadmap-v16/heap-premises.json').read_text())
 statements(ROWS,POLICY);reached=controls(NODES,POLICY)
 for ref in ['HEAD','origin/master']:subprocess.run(['git','merge-base','--is-ancestor',PUB,ref],cwd=ROOT,check=True)
 files=['Compiler','Correct','Stmt','Sim','MemoryCompile','MemoryGrowResult','MemoryObjects','MemoryRefArrayState','MemoryRefArrayCompile','MemoryObjectCompile','MemoryCompileExamples','MemoryObjectArrayExamples','MemoryRefArrayExamples','MemoryAllocSourceExamples','MemoryLoopExamples','MemoryLoopCompile']
 hashes={}
 for f in files:
  path='Solidity/Evm/'+f+'.lean';pub=subprocess.check_output(['git','show',PUB+':'+path],cwd=ROOT)
  core.require((ROOT/path).read_bytes()==pub,'published producer modified: '+path);hashes[path]=core.digest(pub)
 prior='9bf486095cb9faa7a23929c74f4fe79e95caa3f9';reuse='Solidity/Roadmap/V16/SpecificationControls.lean'
 core.require((ROOT/reuse).read_bytes()==subprocess.check_output(['git','show',prior+':'+reuse],cwd=ROOT),'changed approved exhaustion countercontrol')
 pathlib.Path(sys.argv[4]).write_text(json.dumps(dict(head=DATA['inventory']['head'],revision=PUB,producerHashes=hashes,scopedClosure=reached,
  headlineTheorems=sorted(NAMES),closedScopedControls=REQUIRED,actualAxioms={n:ROWS[n]['axioms'] for n in sorted(NAMES)},
  controlLogSha256=[m['rawLogSha256'] for m in METAS],policySha256=core.digest((ROOT/'tests/roadmap-v16/heap-premises.json').read_bytes()),
  auditScriptSha256=core.digest(pathlib.Path(__file__).read_bytes()),allGlobalObligations='OPEN',laneComplete=False,externalByteEvm=False,
  paymentBoundary='funded success and insufficient-funds source/target revert inhabited; source-success/target-refusal candidate arm remains conditional; corrupted oracle is NOT Input',
  divergenceBoundary='actual canonical nonallocating spin Input/Room and source divergence/machine fault, not pinned-EVM resources or termination',
  reusedExhaustionCountercontrol=dict(head=prior,path=reuse,sha256=core.digest((ROOT/reuse).read_bytes()))),indent=2)+'\n')
 unittest.main(argv=[sys.argv[0]],verbosity=2)
