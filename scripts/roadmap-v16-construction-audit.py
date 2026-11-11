#!/usr/bin/env python3
"""Actual memory-object construction/compiler-algebra accounting. Never closes G48-G51."""
import copy,hashlib,importlib.util,json,pathlib,subprocess,sys,unittest
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('core',ROOT/'scripts/roadmap-v16-accounting.py')
core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
PUB='5f6a75b6038371a3917dbe08b660d5f2d1207c58'
PRE='Solidity.Roadmap.V16.'
PROPS={
'allocation_cost':['path'],'result':['path','input'],'rep_iff':['path'],
'success':['path','input','source'],'spec':['path','input','source','box'],
'failure':['path','input','source'],'alias':['repr','left','right'],
'small_frame':['path','small'],'cursor':['path','input','source','positive','allocator','space'],
'not_exhausted':['path','input'],'capacity':['path','input','allocator'],
'diamond':['path','input','diamond'],'diamond_iff':['path','input'],
'diamond_cursor':['path','input','diamond','positive','allocator'],
'box':['path','input','box'],'box_iff':['path','input'],'box_diamond_dual':['path','input'],
'append_cert':['head','tail'],'reconstruct':['path'],'public_cert':['path'],
'compile_inversion':['path','accepted'],'compile_append':['compiledHead','compiledTail'],
'compile_append_link':['link','compiledHead','compiledTail'],
'certificate_code':['path'],'certificate_fragment':['path'],
'public_append_code':['wholePath','headPath','tailPath','link','source','compiledWhole','compiledHead','compiledTail']}
NAMES={PRE+'construction_'+n for n in PROPS}
REQUIRED=['input','cost','source_exists','source','answer','diamond','represented','public_represented',
 'wrong_frame','false_post','no_wrong_revert','source_alias','source_distinct','represented_alias','machine_value',
 'cursor','wrong_value','ordered_transport','boundary.successful_last_cursor','insufficient_capacity',
 'unreachable.input','unreachable.reached_cost','unreachable.exact_revert','bounds.all_three',
 'runtimeZero.represented','runtimeZero.cost','runtimeZero.false_post','runtimeZero.ordered_transport',
 'fixedZero.represented','fixedZero.cost','fixedZero.false_post','fixedZero.ordered_transport',
 'fixedRebind.represented','fixedRebind.cost','fixedRebind.false_post','fixedRebind.ordered_transport','fixedRebind.bounds.all_two',
 'populated.reconstruct_source','populated.prefix_accepted','populated.suffix_accepted','populated.canonical_accepted',
 'populated.code_composes','populated.fragment_composes','populated.entry_populated','populated.entry_pointer',
 'populated.reached_input','populated.composed_specification','populated.staged_old_reference_transport',
 'populated.canonical_old_reference_transport']
CONTROL=PRE+'ConstructionControls.'
def validate_policy(rows,policy):
 core.require(policy['revision']==PUB,'wrong source revision')
 core.require(set(policy['theorems'])==NAMES,'missing/extra theorem policy')
 for name in NAMES:
  core.require(name in rows,'missing actual construction/algebra theorem')
  row=rows[name];core.require(row['premises']==policy['theorems'][name],'altered complete premise telescope')
  short=name.removeprefix(PRE+'construction_')
  core.require([p['name'] for p in row['premises'] if p['isProp']]==PROPS[short],'extra/missing proof premise')
  core.require(not any('PublicCorrectness' in x for x in row['typeConstants']),'desired simulation premise')
  core.require(set(row['axioms'])<=core.AXIOMS,'unapproved actual axiom')
 for suffix in ['compile_inversion','public_append_code']:
  core.require('Solidity.Evm.Compiler.compile' in rows[PRE+'construction_'+suffix]['typeConstants'],'missing actual public compilation function')

def closure(meta):
 nodes={r['name']:r for r in meta['theorems']+meta['definitions']}
 for r in nodes.values():
  core.require('axioms' in r and set(r['axioms'])<=core.AXIOMS,'missing/unapproved helper trust')
 todo=[n for n,r in nodes.items() if r.get('ownerName',n).startswith((PRE+'construction_',PRE+'constructionAppend',PRE+'constructionCompose',PRE+'constructionCertificate',PRE+'constructionShape',CONTROL))]
 seen=set()
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);r=nodes[n];deps=set(r['dependencies'])|set(r['typeConstants'])
  core.require(not any('PublicCorrectness' in x for x in deps),'desired simulation oracle in reached helper')
  for dep in deps:
   owned=dep.startswith(PRE) or (dep.startswith('_private.') and ('.'+PRE in dep or dep.startswith(('_private.Solidity.Roadmap.V16.','_private.Solidity.Examples.Roadmap.V16.'))))
   core.require(not owned or dep in nodes,'missing reached owned helper')
   if dep in nodes and dep not in seen:todo.append(dep)
 return sorted(seen)

def actual_private_splitter(meta):
 reached=set(closure(meta));nodes={r['name']:r for r in meta['theorems']+meta['definitions']}
 for name in sorted(reached):
  if name.startswith('_private.Solidity.Examples.Roadmap.V16.ConstructionCompilation.') and '.splitter' in name:
   if any(name in set(nodes[parent]['dependencies'])|set(nodes[parent]['typeConstants']) for parent in reached if parent!=name):
    return name
 raise core.Invalid('missing actual reached private splitter for countercontrols')

def controls(meta):
 rows={r['name']:r for r in meta['theorems']}
 for suffix in REQUIRED:
  name=CONTROL+suffix;core.require(name in rows,'missing actual constructor/resource combination: '+suffix)
  core.require(not rows[name]['premises'],'premise-only alleged closed witness: '+suffix)
 defs={r['name']:r for r in meta['definitions']}
 origins=[('compiled','MemoryObjectConstructionExamples','compiled'),('P','MemoryObjectConstructionExamples','program'),
 ('runtimeZero.compiled','MemoryObjectConstructionExamples','zeroCompiled'),('fixedZero.compiled','MemoryObjectConstructionExamples','fixedZeroCompiled'),
 ('fixedRebind.compiled','MemoryReferenceArrayRebindExamples','compiled')]
 for owned,module,published in origins:
  core.require(CONTROL+owned in defs,'missing fixture adapter')
  core.require(any(x.startswith('_private.Solidity.Evm.'+module+'.') and x.endswith('.'+published) for x in defs[CONTROL+owned]['dependencies']),'missing actual published compiler/source origin')
 for n in ['prefixCompiled','suffixCompiled']:
  core.require('Solidity.Evm.Compiler.compile' in defs[CONTROL+'populated.'+n]['dependencies'],'staged compiler output is not actual public compilation')
 nodes={r['name']:r for r in meta['theorems']+meta['definitions']}
 # Lean extracts record-field proofs into actual theorem helpers; follow them.
 todo=[CONTROL+'populated.composedCertificate'];seen=set();deps=set()
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);direct=set(nodes[n]['dependencies']);deps|=direct
  todo.extend(d for d in direct if d in nodes and d not in seen)
 core.require(PRE+'constructionCompose' in deps and CONTROL+'populated.reconstruct_source' in deps,'composition adapter provenance missing')
 return closure(meta)

def validate(data,policy,meta):
 inv=data['inventory'];ledger=core.validate_inventory(inv);core.validate_report(data['report'],inv,ledger)
 validate_policy({r['name']:r for r in inv['theorems']},policy)
 core.require(any(r['id']=='constructor:Solidity.Evm.Compiler.Compilation.construction' and r['status']=='open' for r in data['report']['obligations']),'missing/closed constructor obligation')
 core.require(not data['report']['laneComplete'] and all(r['status']=='open' for r in data['report']['obligations']),'unproved coverage closure')
 return controls(meta)

class NegativeControls(unittest.TestCase):
 def test_live(self):validate(DATA,POLICY,META)
 def test_wrong_revision(self):
  p=copy.deepcopy(POLICY);p['revision']='0'*40
  with self.assertRaises(core.Invalid):validate(DATA,p,META)
 def test_absent_policy(self):
  p=copy.deepcopy(POLICY);p['theorems'].pop(next(iter(NAMES)))
  with self.assertRaises(core.Invalid):validate(DATA,p,META)
 def test_same_binder_strengthening(self):
  rows={r['name']:copy.deepcopy(r) for r in DATA['inventory']['theorems']};rows[PRE+'construction_diamond']['premises'][-1]['closedExpr']+=' AND desired run'
  with self.assertRaises(core.Invalid):validate_policy(rows,POLICY)
 def test_extra_success_premise(self):
  rows={r['name']:copy.deepcopy(r) for r in DATA['inventory']['theorems']};rows[PRE+'construction_diamond']['premises'].append(dict(name='desiredRun',isProp=True,type='oracle'))
  with self.assertRaises(core.Invalid):validate_policy(rows,POLICY)
 def test_missing_canonical_combination(self):
  m=copy.deepcopy(META);m['theorems']=[r for r in m['theorems'] if r['name']!=CONTROL+'populated.canonical_old_reference_transport']
  with self.assertRaises(core.Invalid):controls(m)
 def test_premise_only_witness(self):
  m=copy.deepcopy(META);next(r for r in m['theorems'] if r['name']==CONTROL+'populated.reached_input')['premises'].append(dict(name='desiredInput',isProp=True))
  with self.assertRaises(core.Invalid):controls(m)
 def test_fake_published_origin(self):
  m=copy.deepcopy(META);next(r for r in m['definitions'] if r['name']==CONTROL+'compiled')['dependencies']=[]
  with self.assertRaises(core.Invalid):controls(m)
 def test_fake_prefix_origin(self):
  m=copy.deepcopy(META);next(r for r in m['definitions'] if r['name']==CONTROL+'populated.prefixCompiled')['dependencies']=[]
  with self.assertRaises(core.Invalid):controls(m)
 def test_fake_composition_origin(self):
  m=copy.deepcopy(META);next(r for r in m['definitions'] if r['name']==CONTROL+'populated.composedCertificate')['dependencies']=[]
  with self.assertRaises(core.Invalid):controls(m)
 def test_oracle_helper(self):
  m=copy.deepcopy(META);next(r for r in m['definitions'] if r['name']==PRE+'constructionCompose')['dependencies'].append('Solidity.Roadmap.PublicCorrectness')
  with self.assertRaises(core.Invalid):closure(m)
 def test_missing_private_helper(self):
  m=copy.deepcopy(META);next(r for r in m['definitions'] if r['name']==PRE+'constructionCompose')['dependencies'].append('_private.test.0.Solidity.Roadmap.V16.missing')
  with self.assertRaises(core.Invalid):closure(m)
 def test_absent_actual_private_splitter(self):
  m=copy.deepcopy(META)
  name=actual_private_splitter(m)
  for kind in ['theorems','definitions']:m[kind]=[r for r in m[kind] if r['name']!=name]
  with self.assertRaises(core.Invalid):closure(m)
 def test_actual_private_splitter_oracle(self):
  m=copy.deepcopy(META)
  name=actual_private_splitter(m)
  row=next(r for r in m['theorems']+m['definitions'] if r['name']==name)
  row['dependencies'].append('Solidity.Roadmap.PublicCorrectness')
  with self.assertRaises(core.Invalid):closure(m)
 def test_unapproved_definition_axiom(self):
  m=copy.deepcopy(META);m['definitions'][0]['axioms'].append('sorryAx')
  with self.assertRaises(core.Invalid):closure(m)
 def test_unapproved_control_axiom(self):
  m=copy.deepcopy(META);m['theorems'][0]['axioms'].append('sorryAx')
  with self.assertRaises(core.Invalid):closure(m)
 def test_closed_global_obligation(self):
  d=copy.deepcopy(DATA);d['report']['obligations'][0]['status']='closed'
  with self.assertRaises(core.Invalid):validate(d,POLICY,META)
 def test_absent_global_obligation(self):
  d=copy.deepcopy(DATA);d['report']['obligations'].pop()
  with self.assertRaises(core.Invalid):validate(d,POLICY,META)

if __name__=='__main__':
 DATA=json.loads(pathlib.Path(sys.argv[1]).read_text());META=core.snapshot(pathlib.Path(sys.argv[2]))
 POLICY=json.loads((ROOT/'tests/roadmap-v16/construction-premises.json').read_text());reached=validate(DATA,POLICY,META)
 for ref in ['HEAD','origin/master']:subprocess.run(['git','merge-base','--is-ancestor',PUB,ref],cwd=ROOT,check=True)
 files=sorted({str(p.relative_to(ROOT)) for p in (ROOT/'Solidity/Evm').glob('MemoryObject*.lean')}|{'Solidity/Evm/Compiler.lean','Solidity/Evm/MemoryReferenceArrayRebindExamples.lean'})
 hashes={}
 for name in files:
  actual=subprocess.check_output(['git','show',PUB+':'+name],cwd=ROOT)
  core.require((ROOT/name).read_bytes()==actual,'modified published producer: '+name);hashes[name]=hashlib.sha256(actual).hexdigest()
 pathlib.Path(sys.argv[3]).write_text(json.dumps(dict(head=DATA['inventory']['head'],revision=PUB,producerHashes=hashes,scopedClosure=reached,
  policySha256=core.digest((ROOT/'tests/roadmap-v16/construction-premises.json').read_bytes()),auditScriptSha256=core.digest(pathlib.Path(__file__).read_bytes()),
  controlLogSha256=META['rawLogSha256'],headlineTheorems=sorted(NAMES),closedScopedControls=REQUIRED,
  canonicalComposition='proved scoped by actual compiler-function algebra; all concrete premises discharged',
  composedAdapter='actual certificate adapter, separately linked to canonical output in this concrete case',
  allGlobalObligations='OPEN',laneComplete=False,contractDeployment=False,externalByteEvm=False),indent=2)+'\n')
 unittest.main(argv=[sys.argv[0]],verbosity=2)
