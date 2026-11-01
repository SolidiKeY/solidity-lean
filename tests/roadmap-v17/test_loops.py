import copy,importlib.util,json,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
def load(name):
 s=importlib.util.spec_from_file_location(name,ROOT/('scripts/roadmap-v17-'+name+'.py'));m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
l=load('loops');t=load('timing')
class LoopControls(unittest.TestCase):
 def baseline(self,family):
  rows=[]
  for name in ['arrays','arraysIR','records','recordsIR']:
   arr=name.startswith('arrays');ir=name.endswith('IR');rows.append(dict(name=name,viaIR=ir,source=4 if arr else 3,cells=[0,1,2,3,4,128,129,130,63] if arr else [0,1,2,3,128,63],target=[131,128,128,2,4,2,3,4,99] if arr else ([130,0,5,128,3,99] if ir else [130,128,128,128,3,99]),stack=[77],emptyCodeTarget=[128],intrinsicCode='synthetic parser baseline only',isDirect=family=='direct',isScoped=family=='scoped',need=5,frameFits=True,zeroFrameFits=False,prefixBudget=3 if arr else 2))
  return dict(schema=1,family=family,base=1,frame=64,cases=rows,semanticPremisesDischarged=False,releaseClosed=False)
 def raw(self,v):return ('V17_LOOP_BEGIN\n'+json.dumps(v)+'\nV17_LOOP_END\n').encode()
 def test_both_shape_baselines_preserve_distinct_records(self):
  for f in l.CONFIG:
   v=self.baseline(f);self.assertEqual(l.observation(self.raw(v),f),v);self.assertNotEqual(v['cases'][2]['target'],v['cases'][3]['target'])
 def test_mutations(self):
  for family in l.CONFIG:
   for key,value in [('target',[131]),('cells',[0,2,1]),('source',False),('stack',[0]),('need',True),('prefixBudget',0),('viaIR',True),('isDirect',False if family=='direct' else True),('frameFits',False),('zeroFrameFits',True),('emptyCodeTarget',[131,128,128,2,4,2,3,4,99])]:
    v=self.baseline(family);v['cases'][0][key]=value
    with self.subTest(family=family,key=key),self.assertRaises(ValueError):l.observation(self.raw(v),family)
   v=self.baseline(family);v['cases'][3]['target']=v['cases'][2]['target']
   with self.assertRaises(ValueError):l.observation(self.raw(v),family)
 def test_frames_orders_and_promotions(self):
  for f in l.CONFIG:
   v=self.baseline(f);raw=self.raw(v)
   for bad in [raw+raw,raw[:-8],raw.replace(b'"schema": 1',b'"schema": 1,"schema": 1')]:
    with self.assertRaises(ValueError):l.observation(bad,f)
   for key,value in [('cases',v['cases'][::-1]),('family','other'),('releaseClosed',True),('semanticPremisesDischarged',True),('frame',True)]:
    bad=copy.deepcopy(v);bad[key]=value
    with self.assertRaises(ValueError):l.observation(self.raw(bad),f)
 def test_exact_wrapper_forgery(self):
  first={'observation':self.baseline('direct'),'metadata':{'type':'real checked only in live evidence'},'sourceSnapshot':{'revision':'a'},'profile':{'source':'b'},'installedInputs':{'lib':'c'}}
  for field in first:
   bad=copy.deepcopy(first);bad[field]={'forged':'matching producer claim'}
   with self.assertRaises(ValueError):l.creation().load_memory().exact_replay(first,bad)
 def test_queries_are_full_and_relation_specific(self):
  for f in l.CONFIG:
   b=l.query_bytes(f);self.assertEqual(len(l.public_requests(f))+len(l.PRIVATE),16);self.assertIn(b'KernelQuery.extract requests',b);self.assertNotIn(b'includeValues',b.split(b'run_cmd do')[-1]);self.assertNotIn(b'allocationCost',b);self.assertIn(l.CONFIG[f][2].encode()+b'.prefixBudget',b);self.assertFalse(l.publication_identity(f)['finiteAllocationCostUsed'])
class TimingControls(unittest.TestCase):
 def baseline(self):return {'kind':'fresh-original-Derived17-workload','exit_code':0,'budgetSeconds':300,'seconds':240,'expectedModules':t.MODULES,'checks':[{'module':m,'fresh':True,'exit_code':0,'seconds':9,'sourceSha256':'0'*64} for m in t.MODULES]}
 def test_complete_only(self):self.assertEqual(t.validate_shape(self.baseline(),lambda _:'0'*64)['members'],24)
 def test_partial_warm_stale_failed_raised_cumulative_and_bool(self):
  edits=[lambda d:d['checks'].pop(),lambda d:d['checks'][0].update(fresh=False),lambda d:d.update(exit_code=124),lambda d:d.update(exit_code=False),lambda d:d.update(seconds=965.51),lambda d:d.update(budgetSeconds=301),lambda d:d.update(seconds=True),lambda d:d['checks'][0].update(seconds=299),lambda d:d['checks'][0].update(exit_code=True),lambda d:d['checks'][0].update(sourceSha256='1'*64),lambda d:d['checks'].reverse(),lambda d:d.update(expectedModules=[])]
  for edit in edits:
   d=copy.deepcopy(self.baseline());edit(d)
   with self.assertRaises(ValueError):t.validate_shape(d,lambda _:'0'*64)

 def test_post_input_failure_keeps_raw_exit_and_bound_error(self):
  import tempfile
  p=load('provenance')
  with tempfile.TemporaryDirectory() as directory:
   out=Path(directory)
   for raw,cleanup in [(0,0),(124,0),(0,125)]:
    for provider in [lambda: {'changed':True},lambda: (_ for _ in ()).throw(OSError('Python input unavailable'))]:
     record={'commandExit':raw,'executionExit':raw,'cleanupExit':cleanup,'validationExit':0,'phaseErrors':[],'errors':'execution-errors.json'}
     p.post_input_observation(record,'pythonInputs',{'original':True},provider,'Python inputs after',out)
     self.assertEqual(record['commandExit'],raw);self.assertEqual(record['validationExit'],125);self.assertEqual(record['exit'],raw or cleanup or 125)
     self.assertEqual(json.loads((out/record['errors']).read_text()),record['phaseErrors']);self.assertEqual(p.e.digest((out/record['errors']).read_bytes()),record['errorsSha256'])
 def test_timing_python_isolation_bound(self):
  p=load('provenance');cmd=p.gate_command('fresh-derived17',Path('/tmp/receipt'))
  self.assertEqual(cmd[1:4],['-I','-S','-B']);self.assertIn('check-memory-loop-timing.py',cmd[4]);self.assertEqual(cmd[-1],'/tmp/receipt/workload.json')
