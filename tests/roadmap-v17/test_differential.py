"""Host-only orchestration controls; mocks never stand for a native pass."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('differential',ROOT/'scripts/roadmap-v17-differential.py')
d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)

class DifferentialControls(unittest.TestCase):
 def result(self):return {'collectorExit':0,'verificationExit':0,'postInputExit':0,'outputsVerified':True,'rawCommandExit':0}
 def test_phase_priority_never_promotes(self):
  r=self.result();self.assertEqual(d.final_exit(r),0)
  for field,value in [('collectorExit',124),('collectorExit',125),('verificationExit',2),('postInputExit',125),('collectorExit',None),('verificationExit',None),('postInputExit',None),('rawCommandExit',None),('rawCommandExit',124)]:
   row=copy.deepcopy(r);row[field]=value
   with self.subTest(field=field,value=value):self.assertNotEqual(d.final_exit(row),0)
  r['collectorExit']=124;r['verificationExit']=2;r['postInputExit']=125;self.assertEqual(d.final_exit(r),124)
 def test_invalid_phase_types(self):
  for value in (True,-1,'0',256):
   r=self.result();r['collectorExit']=value
   with self.subTest(value=value),self.assertRaises(ValueError):d.final_exit(r)
 def test_no_output_manifest_is_incomplete(self):
  r=self.result();r['outputsVerified']=False;self.assertEqual(d.final_exit(r),2)
 def test_actual_snapshot_identity_and_mutations(self):
  s={'revision':'a'*40,'sourceTree':'b'*40,'runtime':{'lean':{'version':'lean'},'lake':{'version':'lake'}}}
  n={'revision':s['revision'],'tree':s['sourceTree'],'leanVersion':'lean','lakeVersion':'lake','compiler':{'path':str(d.COMPILER),'bytes':10798266,'sha256':d.COMPILER_SHA,'version':'0.8.38+commit.1835d247.Emscripten.clang'},'node':{'path':str(d.NODE.resolve()),'sha256':'c'*64}}
  d.check_native_identity(n,s,{str(d.NODE):'c'*64})
  for key in ('revision','tree','leanVersion','lakeVersion'):
   bad=copy.deepcopy(n);bad[key]='changed'
   with self.subTest(key=key),self.assertRaises(ValueError):d.check_native_identity(bad,s,{str(d.NODE):'c'*64})
  n['compiler']['sha256']='0'*64
  with self.assertRaises(ValueError):d.check_native_identity(n,s,{str(d.NODE):'c'*64})
 def test_input_hash_inventory_mutations(self):
  original={'runner':'a'*64,'compiler':'b'*64,'dependency':'c'*64,'node':'d'*64}
  d.same_inputs(original,copy.deepcopy(original))
  for key in original:
   bad=dict(original);bad[key]='0'*64
   with self.subTest(key=key),self.assertRaises(ValueError):d.same_inputs(original,bad)
  with self.assertRaises(ValueError):d.same_inputs(original,{'runner':'a'*64})
 def test_mounts_preserve_original_hard_limits(self):
  argv=['create','--memory','12g','--memory-swap','12g','--cpus','1',d.p.IMAGE,'sh','run.sh']
  actual=d.mount_runtime(argv,Path('/workspace/scratch/fixture/git-wrapper'))
  self.assertEqual([x for x in actual if x in ('12g','1')],['12g','12g','1'])
  for source,destination in d.LIBRARIES:self.assertIn('type=bind,src='+source+',dst='+destination+',readonly',actual)
  self.assertEqual(actual[-3:],[d.p.IMAGE,'sh','run.sh']);self.assertEqual(argv[0],'create')
 def test_refuse_existing_output_without_launch(self):
  with tempfile.TemporaryDirectory(dir='/workspace/scratch') as tmp,patch.object(d.p,'collect') as launch:
   with self.assertRaises(ValueError):d.collect(Path(tmp))
   launch.assert_not_called()
 def test_preflight_refusal_retained_no_launch(self):
  with tempfile.TemporaryDirectory(dir='/workspace/scratch') as tmp,patch.object(d.p,'ensure_no_unresolved',side_effect=ValueError('existing worker')),patch.object(d.p,'collect') as launch:
   out=Path(tmp)/'new';r=d.collect(out);launch.assert_not_called()
   self.assertIsNone(r['rawCommandExit']);self.assertIsNone(r['collectorExit']);self.assertEqual(r['exit'],2)
   self.assertEqual(json.loads((out/'outcome.json').read_text())['phaseErrors'][0]['error'],'existing worker')
   for key in d.FLAGS:self.assertIs(r[key],False)
 def test_configuration_routes_only_original_command(self):
  with patch.object(d.p,'gate_command',return_value=['original']),patch.object(d.p,'docker_create_argv',return_value=[d.p.IMAGE]):
   old=d.configure(Path('/workspace/scratch/wrapper'))
   try:
    self.assertEqual(d.p.gate_command('runtime-keysort',Path('/workspace/scratch/x')),['original'])
    cmd=d.p.gate_command(d.GATE,Path('/workspace/scratch/x'))
    self.assertEqual(cmd,[str(d.NODE),str(ROOT/'scripts/roadmap-v17-runtime.mjs'),'run','/workspace/scratch/x/result'])
    self.assertEqual(d.p.BUDGET,{'processSeconds':300,'suiteModuleSeconds':300,'leanNumThreads':1})
   finally:d.p.gate_command,d.p.docker_create_argv=old;d.p.TARGETS.pop(d.GATE,None)

 def test_recover_raw_failure_without_authenticating(self):
  with tempfile.TemporaryDirectory(dir='/workspace/scratch') as tmp:
   out=Path(tmp);(out/'execution').mkdir();receipt=out/'execution/provenance.json'
   receipt.write_text(json.dumps({'schema':3,'commandExit':124,'exit':124}))
   result={'receiptValidated':False};d.retain_receipt(out,result)
   self.assertEqual(result['rawCommandExit'],124);self.assertFalse(result['receiptValidated'])
   receipt.write_text(json.dumps({'schema':3,'commandExit':True,'exit':0}))
   with self.assertRaises(ValueError):d.retain_receipt(out,result)
 def test_collector_exception_keeps_raw_receipt_and_postchecks(self):
  with tempfile.TemporaryDirectory(dir='/workspace/scratch') as tmp:
   out=Path(tmp)/'new';snapshot={'revision':'a'*40};files={'source':'b'*64}
   def fail(args):
    args.out.mkdir();(args.out/'provenance.json').write_text(json.dumps({'schema':3,'commandExit':124,'exit':124}))
    raise OSError('transport after receipt')
   with patch.object(d.p,'ensure_no_unresolved'),patch.object(d.e,'snapshot',return_value=snapshot),patch.object(d.subprocess,'check_output',side_effect=lambda argv,**kwargs:(d.ROOT/argv[-1].split(':',1)[1]).read_bytes()),patch.object(d,'input_files',return_value=files) as inputs,patch.object(d.p,'resource_snapshot',return_value={}),patch.object(d.p,'check_headroom'),patch.object(d.p,'collect',side_effect=fail):
    result=d.collect(out)
   self.assertEqual(inputs.call_count,2);self.assertEqual(result['rawCommandExit'],124)
   self.assertIsNone(result['collectorExit']);self.assertEqual(result['verificationExit'],2)
   self.assertFalse(result['receiptValidated']);self.assertEqual(result['postInputExit'],0);self.assertEqual(result['exit'],2)
   self.assertEqual(result['phaseErrors'][0]['error'],'transport after receipt')

 def test_malformed_receipt_still_finalizes(self):
  with tempfile.TemporaryDirectory(dir='/workspace/scratch') as tmp,patch.object(d.p,'ensure_no_unresolved'):
   snapshot={'revision':'a'*40};out=Path(tmp)/'new'
   def fail(args):
    args.out.mkdir();(args.out/'provenance.json').write_text('[]');raise OSError('transport')
   with patch.object(d.e,'snapshot',return_value=snapshot),patch.object(d.subprocess,'check_output',side_effect=lambda argv,**kwargs:(d.ROOT/argv[-1].split(':',1)[1]).read_bytes()),patch.object(d,'input_files',return_value={}) as inputs,patch.object(d.p,'resource_snapshot',return_value={}),patch.object(d.p,'check_headroom'),patch.object(d.p,'collect',side_effect=fail):r=d.collect(out)
   self.assertEqual(inputs.call_count,2);self.assertEqual(r['postInputExit'],0);self.assertEqual(r['exit'],2)
   self.assertEqual(r['phaseErrors'][1]['phase'],'receipt-recovery');self.assertTrue((out/'outcome.json').is_file())
 def test_native_executable_and_full_compiler_mutations(self):
  current={'revision':'r','sourceTree':'t','runtime':{'lean':{'version':'l'},'lake':{'version':'k'}}}
  native={'revision':'r','tree':'t','leanVersion':'l','lakeVersion':'k','node':{'path':str(d.NODE.resolve()),'sha256':'c'*64},'compiler':{'path':str(d.COMPILER),'bytes':10798266,'sha256':d.COMPILER_SHA,'version':'0.8.38+commit.1835d247.Emscripten.clang'}}
  for group,key in [('node','path'),('node','sha256'),('compiler','version'),('compiler','path'),('compiler','bytes')]:
   bad=copy.deepcopy(native);bad[group][key]='changed'
   with self.subTest(group=group,key=key),self.assertRaises(ValueError):d.check_native_identity(bad,current,{str(d.NODE):'c'*64})

 def test_guard_refusal_keeps_numeric_observations(self):
  with tempfile.TemporaryDirectory(dir='/workspace/scratch') as tmp:
   snapshot={'revision':'a'*40};observed={'hostMemAvailableBytes':20*1024**3,'enclosingCgroupLimitBytes':16*1024**3,'enclosingCgroupCurrentBytes':13*1024**3,'headroomBytes':3*1024**3}
   with patch.object(d.p,'ensure_no_unresolved'),patch.object(d.e,'snapshot',return_value=snapshot),patch.object(d.subprocess,'check_output',side_effect=lambda argv,**kwargs:(d.ROOT/argv[-1].split(':',1)[1]).read_bytes()),patch.object(d,'input_files',return_value={}),patch.object(d.p,'resource_snapshot',return_value=observed),patch.object(d.p,'collect') as launch:
    result=d.collect(Path(tmp)/'new')
   launch.assert_not_called();self.assertEqual(result['preflightResources'],observed)
   self.assertEqual(result['exit'],2);self.assertIsNone(result['rawCommandExit'])
