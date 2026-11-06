"""Component protocol controls. Mock bookkeeping tests are never kernel evidence."""
import copy
import hashlib
import importlib.util
import json
import subprocess
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path('/workspace/solidity-lean')
spec=importlib.util.spec_from_file_location('component',ROOT/'scripts/roadmap-v17-components.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)

class ComponentControls(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory(dir='/workspace/scratch/v17-parallel-interface');self.addCleanup(self.tmp.cleanup);self.base=Path(self.tmp.name)
  self.module='Solidity.Fixture';self.sha='c'*64
  self.snapshot={'revision':'a'*40,'sourceTree':'b'*40,'sourceToolchainKey':'c'*64,'inputs':{},'runtime':{},'buildTools':{},'serialConfigSha256':'d'*64,'repository':str(ROOT)}
  path=self.base/'source';path.mkdir();files={'Solidity/Fixture.lean':{'sha256':self.sha,'gitBlob':'e'*40,'mode':'100644'}}
  closure={'order':[self.module],'modules':{self.module:{'source':'Solidity/Fixture.lean','sha256':self.sha,'imports':[]}}}
  for name in c.PROFILE_FILES:files[name]={'sha256':'7'*64,'gitBlob':'8'*40,'mode':'100644'}
  self.source={'schema':1,'sourceOnly':True,'destination':str(path),'package':{'head':'a'*40,'tree':'b'*40,'base':c.e.BASE,'ref':'refs/heads/fixture','bundleSha256':'a'*64,'modules':[self.module]},'snapshot':self.snapshot,'files':files,'moduleClosures':{self.module:closure},'releaseClosed':False,'semanticPremisesDischarged':False}
  gate=self.base/'gate.json';gate.write_text(json.dumps({'before':self.snapshot,'exit':0}))
  ref={'path':str(gate),'sha256':c.e.digest(gate.read_bytes())}
  interface={'modules':{self.module:self.sha},'declarationRequests':[{'name':'Solidity.Fixture.conditional','module':self.module,'kind':'theorem','metadataSha256':None,'propositionPremises':['actual input']}],'profileSha256':c.profile_identity(self.source),'orderedObservations':[]}
  component={'id':'component','stage':c.e.digest(c.canonical(self.source).encode()),'snapshot':self.snapshot,'interface':interface,'requires':{},'mandatoryGates':{'runtime-keysort':ref},'kernelRecords':{self.module:None},'observations':[],'cachePairs':[]}
  self.plan={'schema':1,'ledgerSha256':c.e.digest((ROOT/c.e.LEDGER).read_bytes()),'components':[component],'targetSnapshot':self.snapshot};self.sources={'component':self.source};self.sourceByPath={str(path):self.source}
 def call(self):
  def git(root,*args):
   source=self.sourceByPath[str(root)]
   return (source['snapshot']['sourceTree'] if args[-1]=='HEAD^{tree}' else source['package']['head']).encode()+b'\n'
  with patch.object(c,'safe_config'),patch.object(c,'git',side_effect=git),patch.object(c,'source_inventory',side_effect=lambda root,head:self.sourceByPath[str(root)]['files']),patch.object(c.k,'source_closure',side_effect=lambda mod:self.sourceByPath[str(c.k.ROOT)]['moduleClosures'][mod]),patch.object(c.p,'validate',side_effect=lambda record,*args,**kwargs:record['exit']==0):
   return c.aggregate(self.plan,self.sources)
 def test_baseline_is_component_only_and_conditional(self):
  result=self.call();row=result['components']['component'];self.assertTrue(row['sourceReady']);self.assertFalse(row['retainedEvidenceConsistent']);self.assertIn('conditional-premises-not-discharged',row['obligations']);self.assertIn('missing-retained-kernel-metadata:Solidity.Fixture.conditional',row['obligations']);self.assertEqual(len(result['openRows']),457)
  for flag in ['accountingComplete','semanticPremisesDischarged','releaseClosed']:self.assertIs(result[flag],False)
 def test_missing_source_and_gate_remain_explicit(self):
  self.sources={};row=self.call()['components']['component'];self.assertFalse(row['sourceReady'])
  self.sources={'component':self.source};self.plan['components'][0]['mandatoryGates']['runtime-keysort']=None;row=self.call()['components']['component'];self.assertFalse(row['retainedEvidenceConsistent']);self.assertIn('missing-gate:runtime-keysort',row['obligations'])
 def test_failed_actual_phase_cannot_be_promoted(self):
  ref=self.plan['components'][0]['mandatoryGates']['runtime-keysort'];path=Path(ref['path']);obj=json.loads(path.read_text());obj['exit']=124;path.write_text(json.dumps(obj));ref['sha256']=c.e.digest(path.read_bytes());self.assertFalse(self.call()['components']['component']['retainedEvidenceConsistent'])
 def test_wrong_stage_source_tool_config_module(self):
  baseline=copy.deepcopy(self.plan)
  for key in ['revision','sourceTree','sourceToolchainKey','inputs','runtime','buildTools','serialConfigSha256']:
   self.plan=copy.deepcopy(baseline);self.plan['components'][0]['snapshot']=copy.deepcopy(self.snapshot);self.plan['components'][0]['snapshot'][key]='changed'
   with self.subTest(key=key),self.assertRaises(ValueError):self.call()
  self.plan=copy.deepcopy(baseline);self.plan['components'][0]['interface']['profileSha256']='0'*64
  with self.assertRaisesRegex(ValueError,'profile'):self.call()
  self.plan=copy.deepcopy(baseline);self.plan['components'][0]['interface']['modules'][self.module]='0'*64
  with self.assertRaises(ValueError):self.call()
 def test_corrupt_attachment(self):
  Path(self.plan['components'][0]['mandatoryGates']['runtime-keysort']['path']).write_text('{}')
  with self.assertRaisesRegex(ValueError,'corrupt'):self.call()
 def test_no_semantic_promotion_or_empty_gates(self):
  for flag in ['releaseClosed','semanticPremisesDischarged']:
   self.plan['components'][0]['interface']['declarationRequests'][0][flag]=True
   with self.assertRaises(ValueError):self.call()
   del self.plan['components'][0]['interface']['declarationRequests'][0][flag]
  self.plan['components'][0]['mandatoryGates']={};self.plan['components'][0]['kernelRecords']={}
  with self.assertRaises(ValueError):self.call()
 def test_wrong_ledger_duplicate_component_and_unknown_dependency(self):
  old=self.plan['ledgerSha256'];self.plan['ledgerSha256']='0'*64
  with self.assertRaises(ValueError):self.call()
  self.plan['ledgerSha256']=old;self.plan['components'].append(copy.deepcopy(self.plan['components'][0]))
  with self.assertRaises(ValueError):self.call()
  self.plan['components'].pop();self.plan['components'][0]['requires']={'missing':'0'*64}
  with self.assertRaises(ValueError):self.call()
 def test_observation_order_missing_mismatch_duplicates(self):
  item=self.plan['components'][0];obs={'id':'return/revert','expectedSha256':'e'*64,'artifact':None};item['observations']=[obs];item['interface']['orderedObservations']=[{'id':obs['id'],'sha256':obs['expectedSha256']}]
  row=self.call()['components']['component'];self.assertFalse(row['retainedEvidenceConsistent']);self.assertIn('missing-observation:return/revert',row['obligations'])
  item['interface']['orderedObservations'][0]['sha256']='f'*64
  with self.assertRaises(ValueError):self.call()
  item['interface']['orderedObservations'][0]['sha256']='e'*64;item['observations'].append(copy.deepcopy(obs));item['interface']['orderedObservations'].append(copy.deepcopy(item['interface']['orderedObservations'][0]))
  with self.assertRaises(ValueError):self.call()
 def test_missing_producer_and_interface_mismatch(self):
  consumer=copy.deepcopy(self.plan['components'][0]);consumer['id']='consumer';consumer['requires']={'component':c.e.digest(c.canonical(self.plan['components'][0]['interface']).encode())};self.plan['components'].append(consumer);self.sources={'consumer':self.source};row=self.call()['components']['consumer'];self.assertFalse(row['requiredProducerSourcesReady']);self.assertIn('missing-producer:component',row['obligations'])
  consumer['requires']['component']='0'*64
  with self.assertRaisesRegex(ValueError,'interface'):self.call()
 def test_cycle(self):
  one=self.plan['components'][0];two=copy.deepcopy(one);two['id']='two';one['requires']={'two':c.e.digest(c.canonical(two['interface']).encode())};two['requires']={'component':c.e.digest(c.canonical(one['interface']).encode())};self.plan['components'].append(two);self.sources['two']=self.source
  with self.assertRaisesRegex(ValueError,'cyclic'):self.call()
 def test_extra_package(self):
  self.sources['extra']=self.source
  with self.assertRaises(ValueError):self.call()

 def test_kernel_replay_adapter_retains_parameterized_obligations(self):
  item=self.plan['components'][0];item['mandatoryGates']={};self.snapshot['repository']=self.source['destination'];item['stage']=c.e.digest(c.canonical(self.source).encode())
  row={'name':'Solidity.Fixture.conditional','module':self.module,'kind':'theorem','typeSha256':'1'*64,'valueSha256':'2'*64,'axioms':['propext'],'propositionBinders':[0]}
  item['interface']['declarationRequests'][0]['metadataSha256']=c.e.digest(c.k.canonical(row))
  record={'schema':1,'request':{'schema':1,'module':self.module,'declarations':[{'name':row['name'],'kind':row['kind']}]},'before':self.snapshot,'exit':0,'result':{'rows':[row]}}
  refs={}
  for label in ['record','replay']:
   path=self.base/(label+'.json');path.write_text(json.dumps(record));refs[label]={'path':str(path),'sha256':c.e.digest(path.read_bytes())}
  item['kernelRecords']={self.module:refs}
  with patch.object(c.k,'validate_record',return_value={'module':self.module}),patch.object(c.k,'match_replay') as replay:
   result=self.call();d=result['components']['component'];self.assertTrue(d['retainedEvidenceConsistent']);self.assertEqual(d['retainedDeclarationMetadata'][row['name']]['axioms'],['propext']);self.assertIn('checked-conditional-premises-not-discharged:'+row['name'],d['obligations']);self.assertFalse(result['releaseClosed']);self.assertNotIn('source-declarations-not-checked-metadata',d['obligations']);replay.assert_called_once()
  good=item['interface']['declarationRequests'][0]['metadataSha256'];item['interface']['declarationRequests'][0]['metadataSha256']='0'*64
  with patch.object(c.k,'validate_record',return_value={'module':self.module}),patch.object(c.k,'match_replay'),self.assertRaisesRegex(ValueError,'exact checked'):self.call()
  item['interface']['declarationRequests'][0]['metadataSha256']=good
  del refs['replay']
  with self.assertRaises(ValueError):self.call()
 def test_failed_replay_is_component_pending_not_aggregate_promotion(self):
  item=self.plan['components'][0];item['mandatoryGates']={};self.snapshot['repository']=self.source['destination'];item['stage']=c.e.digest(c.canonical(self.source).encode())
  request={'schema':1,'module':self.module,'declarations':[{'name':'Solidity.Fixture.conditional','kind':'theorem'}]};records={'record':{'schema':1,'request':request,'exit':0,'before':self.snapshot},'replay':{'schema':1,'exit':2,'before':self.snapshot,'request':request,'commandExit':None,'launched':False,'phase':'preflight','error':'effective reserve','semanticPremisesDischarged':False,'releaseClosed':False}}
  refs={}
  for label,value in records.items():
   path=self.base/(label+'.json');path.write_text(json.dumps(value));refs[label]={'path':str(path),'sha256':c.e.digest(path.read_bytes())}
  item['kernelRecords']={self.module:refs}
  result=self.call();row=result['components']['component'];self.assertFalse(row['retainedEvidenceConsistent']);self.assertEqual(row['retainedDeclarationMetadata'],{});self.assertEqual(row['kernelFailures'][0]['exit'],2);self.assertIsNone(row['kernelFailures'][0]['commandExit']);self.assertFalse(result['releaseClosed'])

 def test_mixed_failed_pair_rejects_wrong_request_stale_success_and_promotion(self):
  item=self.plan['components'][0];item['mandatoryGates']={};self.snapshot['repository']=self.source['destination'];item['stage']=c.e.digest(c.canonical(self.source).encode())
  req={'schema':1,'module':self.module,'declarations':[{'name':'Solidity.Fixture.conditional','kind':'theorem'}]}
  baseline={'record':{'schema':1,'request':req,'exit':0,'before':self.snapshot},'replay':{'schema':1,'request':req,'exit':2,'before':self.snapshot,'commandExit':None,'launched':False}}
  for label,mutate in [('wrong-request',lambda rs:rs['replay']['request']['declarations'][0].__setitem__('name','Solidity.Fixture.wrong')),('stale-success',lambda rs:rs['record'].__setitem__('before',dict(self.snapshot,revision='9'*40))),('promoted-success',lambda rs:rs['record'].__setitem__('releaseClosed',True))]:
   records=copy.deepcopy(baseline);mutate(records);refs={}
   for key,value in records.items():
    path=self.base/(label+key+'.json');path.write_text(json.dumps(value));refs[key]={'path':str(path),'sha256':c.e.digest(path.read_bytes())}
   item['kernelRecords']={self.module:refs}
   with self.subTest(label=label),self.assertRaises(ValueError):self.call()

 def test_shared_source_conflict_keeps_individual_results_open(self):
  other=copy.deepcopy(self.source);path=self.base/'other';path.mkdir();other['destination']=str(path);other['files']['Solidity/Fixture.lean']['sha256']='9'*64;other['moduleClosures'][self.module]['modules'][self.module]['sha256']='9'*64
  spec=copy.deepcopy(self.plan['components'][0]);spec['id']='other';spec['stage']=c.e.digest(c.canonical(other).encode());spec['interface']['modules'][self.module]='9'*64
  self.plan['components'].append(spec);self.sources['other']=other;self.sourceByPath[str(path)]=other
  result=self.call();self.assertEqual(len(result['jointSourceConflicts']),1);self.assertTrue(result['components']['component']['sourceReady']);self.assertTrue(result['components']['other']['sourceReady']);self.assertFalse(result['accountingComplete']);self.assertIn('joint-source-conflict:'+self.module,result['components']['other']['obligations'])

 def test_grandchild_readiness_is_transitive(self):
  one=self.plan['components'][0];two=copy.deepcopy(one);two['id']='two';three=copy.deepcopy(one);three['id']='three'
  two['requires']={'component':c.e.digest(c.canonical(one['interface']).encode())};three['requires']={'two':c.e.digest(c.canonical(two['interface']).encode())};self.plan['components']=[three,two,one];self.sources={'two':self.source,'three':self.source}
  result=self.call()['components'];self.assertFalse(result['three']['requiredProducerSourcesReady']);self.assertFalse(result['three']['requiredProducerEvidenceConsistent']);self.assertEqual(result['three']['unreadyRequiredSourceComponents'],['component'])
  self.sources['component']=self.source;result=self.call()['components'];self.assertTrue(result['three']['requiredProducerSourcesReady']);self.assertFalse(result['three']['requiredProducerEvidenceConsistent']);self.assertIn('component',result['three']['unreadyRequiredEvidenceComponents'])

 def test_wrong_package_base_tree_schema_are_not_trusted(self):
  original=copy.deepcopy(self.source)
  for key,value in [('base','0'*40),('tree','0'*40),('bundleSha256','bad'),('modules',[]),('modules',[self.module,self.module]),('modules',['SolidityBridge.NotACoreRoot']),('ref','refs/heads/wrong ref')]:
   self.source=copy.deepcopy(original);self.source['package'][key]=value;self.sources['component']=self.source;self.sourceByPath[self.source['destination']]=self.source;self.plan['components'][0]['stage']=c.e.digest(c.canonical(self.source).encode())
   with self.subTest(key=key),self.assertRaises(ValueError):self.call()
  self.source=copy.deepcopy(original);self.source['schema']=True;self.sources['component']=self.source;self.plan['components'][0]['stage']=c.e.digest(c.canonical(self.source).encode())
  with self.assertRaises(ValueError):self.call()
 def test_actual_orphan_source_is_rejected_before_gate_accounting(self):
  root=self.base/'orphan';root.mkdir();c.git(root,'init','--template=');(root/'file').write_text('orphan')
  c.git(root,'add','file');c.git(root,'-c','user.name=V17 control','-c','user.email=control@local.invalid','commit','-m','orphan rejection control')
  orphan=copy.deepcopy(self.source);orphan['destination']=str(root);orphan['package']['head']=c.git(root,'rev-parse','HEAD').decode().strip();orphan['package']['tree']=c.git(root,'rev-parse','HEAD^{tree}').decode().strip();orphan['snapshot']=copy.deepcopy(self.snapshot);orphan['snapshot']['revision']=orphan['package']['head'];orphan['snapshot']['sourceTree']=orphan['package']['tree']
  self.plan['components'][0]['stage']=c.e.digest(c.canonical(orphan).encode());self.plan['components'][0]['snapshot']=orphan['snapshot']
  with self.assertRaises(subprocess.CalledProcessError):c.aggregate(self.plan,{'component':orphan})

 def test_private_fsmonitor_and_filters_never_execute(self):
  root=self.base/'unsafe-config';root.mkdir();c.git(root,'init','--template=');sentinel=root/'executed'
  for key in ['core.fsmonitor','filter.peer.clean']:
   c.git(root,'config',key,'touch '+str(sentinel))
   with self.subTest(key=key),self.assertRaisesRegex(ValueError,'configuration'):c.safe_config(root)
   self.assertFalse(sentinel.exists());c.git(root,'config','--unset',key)

 def test_actual_multi_worktree_without_optional_config_extension(self):
  root=self.base/'git-parent';root.mkdir();c.git(root,'init','--template=');(root/'file').write_text('x');c.git(root,'add','file');c.git(root,'-c','user.name=V17 control','-c','user.email=control@local.invalid','commit','-m','private worktree config control')
  child=self.base/'git-child';c.git(root,'worktree','add','--detach',str(child),'HEAD');c.safe_config(root);c.safe_config(child)

 def target(self,exits=(0,0),replay_error=False,post_error=False,consumer_changed=False,target_changed=False,unexpected_axiom=False):
  request={'schema':1,'module':self.module,'declarations':[{'name':'Solidity.Fixture.conditional','kind':'theorem'}]};out=self.base/'target';calls=[];inventory_calls=[]
  row={'name':'Solidity.Fixture.conditional','module':self.module,'kind':'theorem','typeSha256':'1'*64,'valueSha256':'2'*64,'axioms':['sorryAx'] if unexpected_axiom else ['propext'],'propositionBinders':[0]}
  def collect(req,directory):
   directory.mkdir();code=exits[len(calls)];record={'exit':code,'commandExit':code if code!=124 else None,'result':{'rows':[row]}};(directory/'record.json').write_text(json.dumps(record));calls.append(code);return record
  def inventory(root,head):
   inventory_calls.append(1)
   if post_error and len(inventory_calls)>1:raise ValueError('changed source after command')
   return self.source['files']
  def replay(*args):
   if replay_error:raise ValueError('contradictory replay')
  with patch.object(c,'consumer_identity',side_effect=[{'snapshot':self.snapshot,'helpers':{}},{'snapshot':dict(self.snapshot,revision='f'*40) if consumer_changed else self.snapshot,'helpers':{}}]),patch.object(c,'git',return_value=('a'*40).encode()),patch.object(c,'source_inventory',side_effect=inventory),patch.object(c.e,'snapshot',side_effect=[self.snapshot,dict(self.snapshot,revision='e'*40) if target_changed else self.snapshot]),patch.object(c.k,'collect',side_effect=collect),patch.object(c.k,'validate_record'),patch.object(c.k,'match_replay',side_effect=replay):
   result=c.collect_target(self.source,request,out)
  return result,calls
 def test_per_target_api_success_preserves_conditional_scope(self):
  result,calls=self.target();self.assertEqual(calls,[0,0]);self.assertEqual(result['exit'],0);self.assertTrue(result['completeLiveReplayMatched']);self.assertFalse(result['semanticPremisesDischarged']);self.assertEqual(result['checkedDeclarations'][0]['propositionBinders'],[0])
 def test_per_target_api_timeout_does_not_launch_replay(self):
  result,calls=self.target((124,0));self.assertEqual(calls,[124]);self.assertEqual(result['recordExit'],124);self.assertIsNone(result['recordCommandExit']);self.assertEqual(result['exit'],124);self.assertNotIn('completeLiveReplayMatched',result)
 def test_per_target_api_replay_and_post_failure_remain_failures(self):
  result,_=self.target(replay_error=True);self.assertEqual(result['recordExit'],0);self.assertEqual(result['replayExit'],0);self.assertEqual(result['exit'],2)
 def test_per_target_api_post_failure_does_not_overwrite_raw_success(self):
  result,_=self.target(post_error=True);self.assertEqual(result['recordExit'],0);self.assertEqual(result['replayExit'],0);self.assertEqual(result['postInputExit'],125);self.assertEqual(result['exit'],125)

 def test_per_target_changed_consumer_revision_and_producer_head_are_failed(self):
  result,_=self.target(consumer_changed=True);self.assertEqual(result['postInputExit'],125);self.assertEqual(result['recordExit'],0);self.assertEqual(result['exit'],125)
 def test_per_target_same_tree_producer_revision_move_is_failed(self):
  result,_=self.target(target_changed=True);self.assertEqual(result['postInputExit'],125);self.assertEqual(result['replayExit'],0);self.assertEqual(result['exit'],125)
 def test_dirty_consumer_refuses_before_any_kernel_launch(self):
  request={'schema':1,'module':self.module,'declarations':[{'name':'Solidity.Fixture.conditional','kind':'theorem'}]}
  with patch.object(c,'consumer_identity',side_effect=ValueError('dirty consumer')),patch.object(c.k,'collect') as launch,self.assertRaisesRegex(ValueError,'dirty consumer'):
   c.collect_target(self.source,request,self.base/'refused')
  launch.assert_not_called();self.assertFalse((self.base/'refused').exists())

 def test_per_target_unexpected_axiom_is_retained_but_not_approved(self):
  result,_=self.target(unexpected_axiom=True);self.assertEqual(result['recordExit'],0);self.assertEqual(result['replayExit'],0);self.assertEqual(result['unexpectedAxioms'],['sorryAx']);self.assertEqual(result['exit'],1);self.assertFalse(result['releaseClosed'])

class PairControls(unittest.TestCase):
 def pair(self):
  snapshot={'revision':'a'*40};clean={'mode':'clean','gate':'clean-compiler','before':snapshot,'after':snapshot,'exit':0,'buildStart':{'files':{}},'cacheStart':{'files':{}},'buildEnd':{'path':'build','files':{'a':'b'}},'cacheEnd':{'path':'cache','files':{'x':'y'}}};warm=copy.deepcopy(clean);warm['mode']='warm';warm['gate']='warm-compiler';warm['buildStart']=copy.deepcopy(clean['buildEnd']);warm['cacheStart']=copy.deepcopy(clean['cacheEnd']);return clean,warm
 def test_identity_only_never_gate_validation(self):
  result=c.p.pair_consistency(*self.pair());self.assertTrue(result['pairIdentityMatched']);self.assertFalse(result['accountingComplete'])
 def test_changed_source_budgetless_status_cache_and_artifacts(self):
  for field,value in [('before',{}),('mode','clean'),('exit',124),('exit',False),('gate','warm-frontend'),('buildStart',{'files':{}}),('cacheStart',{'files':{}}),('buildEnd',{'path':'build','files':{'a':'changed'}})]:
   a,b=self.pair();b[field]=value
   with self.subTest(field=field),self.assertRaises(ValueError):c.p.pair_consistency(a,b)

 def test_post_snapshot_keeps_hardened_git_and_restores_adapter(self):
  original=c.e.git
  with patch.object(c,'git',return_value=b'hardened\n') as git,patch.object(c.e,'snapshot',side_effect=lambda root:c.e.git(root,'status','--porcelain')):
   self.assertEqual(c.hardened_snapshot(ROOT),'hardened');git.assert_called_once_with(ROOT,'status','--porcelain')
  self.assertIs(c.e.git,original)

class ActualRetainedControls(unittest.TestCase):
 def test_authentic_old_gate_and_warm_as_clean_corruption(self):
  directory=Path('/workspace/scratch/v17-runtime-correction/keysort');record=c.e.load(directory/'provenance.json');self.assertTrue(c.p.validate(record,directory,record['before'],'runtime-keysort',live_outputs=False))
  for key,value in [('mode','clean'),('commandExit',124),('budgets',{}),('exit',False)]:
   bad=copy.deepcopy(record);bad[key]=value
   with self.subTest(key=key),self.assertRaises(ValueError):c.p.validate(bad,directory,record['before'],'runtime-keysort',live_outputs=False)
 def test_actual_private_client_exact_metadata_and_scoped_axiom_pins(self):
  pins=c.e.load(ROOT/'tests/roadmap-v17/requests/parallel-interface.json');directory=Path('/workspace/scratch/v17-parallel-interface/peer-client-final-kernel');record=c.e.load(directory/'record.json')
  self.assertEqual(record['exit'],0);self.assertEqual(record['before']['revision'],pins['privateCandidateHead']);self.assertEqual(c.p.resources.hash_file(ROOT/'tests/roadmap-v17/ParallelInterface.lean'),pins['consumerSha256']);self.assertEqual(len(record['result']['rows']),5)
  for actual,expected in zip(record['result']['rows'],pins['declarations']):
   self.assertEqual(c.e.digest(c.k.canonical(actual)),expected['metadataSha256']);self.assertEqual(actual['axioms'],['propext'])
   for key in ['name','module','kind','typeSha256','valueSha256','propositionBinders']:self.assertEqual(actual[key],expected[key])
  raw=c.p.read_bound(directory,'axioms.stdout',record['attachments']['axioms.stdout']);c.k.check_axiom_text(raw,record['result']['rows']);bad=copy.deepcopy(record['result']['rows']);bad[0]['axioms']=[]
  with self.assertRaises(ValueError):c.k.check_axiom_text(raw,bad)
 def test_stage_refuses_changed_bundle_identity_and_reuse_before_clone(self):
  request=c.e.load(Path('/workspace/scratch/v17-parallel-interface/own-checkpoint-request.json'));bundle=Path('/workspace/scratch/v17-runtime-correction/v17.bundle')
  request['bundleSha256']='0'*64
  with self.assertRaisesRegex(ValueError,'bundle bytes'):c.stage(bundle,request,Path('/workspace/scratch/v17-parallel-interface/never-created-control'))
  self.assertFalse(Path('/workspace/scratch/v17-parallel-interface/never-created-control').exists())
  with self.assertRaisesRegex(ValueError,'destination'):c.stage(bundle,request,Path('/workspace/scratch/v17-parallel-interface/own-checkpoint-source'))
if __name__=='__main__':unittest.main()
