#!/usr/bin/env python3
"""Actual loop certificate premise/revision accounting. Never closes coverage."""
import json,pathlib,sys,importlib.util,subprocess,hashlib,copy,unittest
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('core',ROOT/'scripts/roadmap-v16-accounting.py')
core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
PUB='5f6a75b6038371a3917dbe08b660d5f2d1207c58'
NAMES=['Solidity.Roadmap.V16.'+p+'_'+s for p in ['loop','scoped_loop'] for s in ['result','not_exhausted','diamond','box','divergence','reconstruct','public_diamond']]
FILES=['Solidity/Evm/Compiler.lean','Solidity/Evm/MemoryCompileExamples.lean','Solidity/Evm/MemoryLoopCompile.lean','Solidity/Evm/MemoryLoopScopeSound.lean','Solidity/Evm/MemoryLoopSourceExamples.lean','Solidity/Evm/MemoryLoopScopeSourceExamples.lean']
def validate(data,policy):
 inv=data['inventory'];ledger=core.validate_inventory(inv);core.validate_report(data['report'],inv,ledger)
 core.require(policy['revision']==PUB,'wrong policy revision')
 core.require(set(policy['theorems'])==set(NAMES),'absent/duplicate theorem policy')
 rows={t['name']:t for t in inv['theorems']}
 validate_premises(rows,policy)
 for suffix in ['memoryLoops','memoryLoopScopes']:
  core.require(any(o['id']=='constructor:Solidity.Evm.Compiler.Compilation.'+suffix and o['status']=='open' for o in data['report']['obligations']),'absent/closed compiler arm')
 core.require(not data['report']['laneComplete'] and all(o['status']=='open' for o in data['report']['obligations']),'coverage falsely closed')
 return rows
def validate_premises(rows,policy):
 for n in NAMES:
  core.require(n in rows,'absent actual loop theorem')
  r=rows[n];core.require(r['premises']==policy['theorems'][n],'strengthened/missing/premise-only transport')
  core.require(n.endswith('_reconstruct') or 'Solidity.Evm.Compiler.Compilation.Input' in r['typeConstants'],'missing actual compiler Input')
  core.require(not any('PublicCorrectness' in x for x in r['typeConstants']),'assumed desired simulation')
  core.require(set(r['axioms'])<=core.AXIOMS,'unapproved trust')
def closure(meta):
 for row in meta['theorems']:core.require(set(row['axioms'])<=core.AXIOMS,'unapproved actual control axiom')
 nodes={r['name']:r for r in meta['theorems']+meta['definitions']}
 prefix='Solidity.Roadmap.V16.'
 todo=[n for n,r in nodes.items() if any(r.get('ownerName',n).startswith(prefix+x) for x in ['loop_','scoped_loop_','MemoryLoopControls.'])]
 seen=set()
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);r=nodes[n];deps=set(r.get('dependencies',[]))|set(r.get('typeConstants',[]))
  core.require(not any('PublicCorrectness' in x for x in deps),'simulation oracle in reached helper')
  for dep in deps:
   owned=dep.startswith(prefix) or (dep.startswith('_private.') and '.'+prefix in dep)
   core.require(not owned or dep in nodes,'missing reached owned helper')
   if dep in nodes and dep not in seen:todo.append(dep)
 return sorted(seen)
RESOURCE_NAMES=['directFailure.exact_revert','scopedFailure.exact_revert','skippedFailure.success','allocSuccess.represented','scopeAllocSuccess.represented','allocFailure.prefix_allocation_revert','scopeAllocFailure.prefix_allocation_revert','capacity.demand_one','capacity.full_state_repr','capacity.full_input_refused','capacity.legacy_query_would_admit','allocatingNonreturn.input','allocatingNonreturn.source','allocatingNonreturn.target','allocatingNonreturn.full_input_refused','skippedFull.input','skippedFull.syntactic_allocation','skippedFull.represented','blockAllocation.input','blockAllocation.final_context_frame_refused','blockAllocation.represented']
def validate_resource(meta):
 rows={r['name']:r for r in meta['theorems']}
 for name in RESOURCE_NAMES:
  full='Solidity.Roadmap.V16.MemoryLoopControls.'+name
  core.require(full in rows,'missing actual resource combination: '+name)
  core.require(not rows[full]['premises'],'premise-only resource witness: '+name)
 origins={r['name']:r['dependencies'] for r in meta['definitions']}
 wanted=[('directFailure','MemoryLoopExamples','badCompiled'),('scopedFailure','MemoryLoopScopeExamples','revertingPublic'),('skippedFailure','MemoryLoopScopeExamples','zeroPublic'),('allocSuccess','MemoryLoopAllocExamples','publicResult'),('allocFailure','MemoryLoopAllocExamples','failingPublic'),('scopeAllocSuccess','MemoryLoopScopeAllocExamples','publicResult'),('scopeAllocFailure','MemoryLoopScopeAllocExamples','failingPublic'),('allocatingNonreturn','MemoryLoopScopeAllocExamples','allocatingSpinPublic'),('skippedFull','MemoryLoopScopeAllocExamples','skippedPublic'),('blockAllocation','MemoryLoopScopeAllocExamples','blockAutomatic')]
 for case,module,name in wanted:
  node='Solidity.Roadmap.V16.MemoryLoopControls.'+case+'.compiled'
  core.require(any(dep.startswith('_private.Solidity.Evm.'+module+'.') and dep.endswith('.'+name) for dep in origins.get(node,[])),'missing actual resource compiler origin: '+case)
 return closure(meta)
class Controls(unittest.TestCase):
 def test_positive(self):validate(DATA,POLICY)
 def test_wrong_revision(self):
  p=copy.deepcopy(POLICY);p['revision']='0'*40
  with self.assertRaises(core.Invalid):validate(DATA,p)
 def test_missing_policy(self):
  p=copy.deepcopy(POLICY);p['theorems'].pop(NAMES[0])
  with self.assertRaises(core.Invalid):validate(DATA,p)
 def test_extra_success_premise(self):
  d=copy.deepcopy(DATA);next(r for r in d['inventory']['theorems'] if r['name']==NAMES[2])['premises'].append({'name':'sourceSuccess','type':'desired source success'})
  with self.assertRaises(core.Invalid):validate(d,POLICY)
 def test_same_binder_strengthening(self):
  d=copy.deepcopy(DATA);next(r for r in d['inventory']['theorems'] if r['name']==NAMES[2])['premises'][-1]['closedExpr']+=' AND desired target run'
  with self.assertRaises(core.Invalid):validate_premises({r['name']:r for r in d['inventory']['theorems']},POLICY)
 def test_closed_arm(self):
  d=copy.deepcopy(DATA);next(o for o in d['report']['obligations'] if o['id']=='constructor:Solidity.Evm.Compiler.Compilation.memoryLoops')['status']='closed'
  with self.assertRaises(core.Invalid):validate(d,POLICY)
 def test_simulation_oracle(self):
  d=copy.deepcopy(DATA);next(r for r in d['inventory']['theorems'] if r['name']==NAMES[0])['typeConstants'].append('Solidity.Roadmap.PublicCorrectness')
  with self.assertRaises(core.Invalid):validate(d,POLICY)
 def test_private_helper_oracle(self):
  m=copy.deepcopy(META);root=next(r for r in m['theorems'] if r['name']==NAMES[0]);alias='_private.LoopAudit.0.Solidity.Roadmap.V16.oracle'
  root['dependencies'].append(alias);m['definitions'].append(dict(name=alias,dependencies=['Solidity.Roadmap.PublicCorrectness']))
  with self.assertRaises(core.Invalid):closure(m)
 def test_missing_helper(self):
  m=copy.deepcopy(META);next(r for r in m['theorems'] if r['name']==NAMES[0])['dependencies'].append('Solidity.Roadmap.V16.missing')
  with self.assertRaises(core.Invalid):closure(m)
 def test_corrupted_control_axiom(self):
  m=copy.deepcopy(META);m['theorems'][0]['axioms'].append('sorryAx')
  with self.assertRaises(core.Invalid):closure(m)
 def test_direct_extra_success_premise(self):
  rows={r['name']:copy.deepcopy(r) for r in DATA['inventory']['theorems']}
  rows[NAMES[2]]['premises'].append(dict(name='desiredRun',type='oracle'))
  with self.assertRaises(core.Invalid):validate_premises(rows,POLICY)
 def test_absent_resource_combination(self):
  m=copy.deepcopy(RESOURCE_META);name='Solidity.Roadmap.V16.MemoryLoopControls.'+RESOURCE_NAMES[0]
  m['theorems']=[r for r in m['theorems'] if r['name']!=name]
  with self.assertRaises(core.Invalid):validate_resource(m)
 def test_premise_only_resource_witness(self):
  m=copy.deepcopy(RESOURCE_META);name='Solidity.Roadmap.V16.MemoryLoopControls.'+RESOURCE_NAMES[0]
  next(r for r in m['theorems'] if r['name']==name)['premises'].append(dict(name='desiredTarget',type='oracle'))
  with self.assertRaises(core.Invalid):validate_resource(m)
 def test_resource_compiler_origin(self):
  m=copy.deepcopy(RESOURCE_META)
  next(r for r in m['definitions'] if r['name']=='Solidity.Roadmap.V16.MemoryLoopControls.blockAllocation.compiled')['dependencies']=[]
  with self.assertRaises(core.Invalid):validate_resource(m)
 def test_corrupted_resource_axiom(self):
  m=copy.deepcopy(RESOURCE_META);m['theorems'][0]['axioms'].append('sorryAx')
  with self.assertRaises(core.Invalid):validate_resource(m)
if __name__=='__main__':
 DATA=json.loads(pathlib.Path(sys.argv[1]).read_text());POLICY=json.loads((ROOT/'tests/roadmap-v16/loop-premises.json').read_text())
 META=core.snapshot(pathlib.Path(sys.argv[2]));reached=closure(META)
 core.require(len(sys.argv)>4,'missing separately checked resource-control metadata')
 RESOURCE_META=core.snapshot(pathlib.Path(sys.argv[4]));resource_reached=validate_resource(RESOURCE_META)
 origins={r['name']:r['dependencies'] for r in META['definitions']}
 for mode,module in [('direct','MemoryLoopSourceExamples'),('scope','MemoryLoopScopeSourceExamples')]:
  for example in ['Arrays','ArraysIR','Records','RecordsIR']:
   prefix='Solidity.Roadmap.V16.MemoryLoopControls.'+mode+example+'.'
   for owned,suffix in [('compiled','compiled'+example),('out','checked'+example)]:
    core.require(any(dep.startswith('_private.Solidity.Evm.'+module+'.') and dep.endswith('.'+suffix) for dep in origins.get(prefix+owned,[])),'missing actual public fixture origin')
 validate(DATA,POLICY)
 for ref in ['HEAD','origin/master']:subprocess.run(['git','merge-base','--is-ancestor',PUB,ref],cwd=ROOT,check=True)
 hashes={}
 FILES=sorted(set(FILES)|{str(p.relative_to(ROOT)) for p in (ROOT/'Solidity/Evm').glob('MemoryLoop*.lean')})
 for f in FILES:
  published=subprocess.check_output(['git','show',PUB+':'+f],cwd=ROOT)
  core.require((ROOT/f).read_bytes()==published,'producer changed: '+f);hashes[f]=hashlib.sha256(published).hexdigest()
 if len(sys.argv)>3:
  pathlib.Path(sys.argv[3]).write_text(json.dumps(dict(revision=PUB,head=DATA['inventory']['head'],producerHashes=hashes,auditScriptSha256=core.digest(pathlib.Path(__file__).read_bytes()),policySha256=core.digest((ROOT/'tests/roadmap-v16/loop-premises.json').read_bytes()),scopedClosure=reached,controlLogSha256=META['rawLogSha256'],resourceLogSha256=RESOURCE_META['rawLogSha256'],resourceClosure=resource_reached,resourceTheorems=RESOURCE_NAMES,theorems=NAMES,laneComplete=False,allObligations='OPEN',externalEvm=False),indent=2)+'\n')
 unittest.main(argv=[sys.argv[0]],verbosity=2)
