#!/usr/bin/env python3
import copy
import importlib.util
import os
import json
from pathlib import Path
import resource
import unittest
from unittest.mock import patch
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(60,)*2)
path=Path(__file__).resolve().parents[2]/'scripts/roadmap-v17-process-identity.py'
spec=importlib.util.spec_from_file_location('identity',path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
CID='a'*64;SHA='b'*64;GROUP='/docker/'+CID

def stat_text(pid,start=1000,state='R'):
    return str(pid)+' (lean) '+ ' '.join([state]+['0']*18+[str(start)]+['0']*32)

def observation(pid=123):
    fd=dict(device=1,inode=2,size=9024,mtimeNs=3,ctimeNs=4)
    return dict(pid=pid,beginBootNs=200*10**9,endBootNs=200*10**9+1000,
      beforeStat=stat_text(pid),afterStat=stat_text(pid),beforeCgroup='0::'+GROUP+'\n',afterCgroup='0::'+GROUP+'\n',
      executableBefore=fd,executableAfter=fd.copy(),executableAssociationAfter=fd.copy(),executableSha256=SHA,
      serializerLock=dict(target=m.LOCK,device=1,inode=9),**m.FLAGS)

def pre_observation():
    x=observation();x['beginBootNs']=50*10**9;x['endBootNs']=50*10**9+1000;return x

def enrich(raw):return m.enrich_live_sample(raw,expected(),100*10**9,100*10**9+1000,{123:pre_observation()})

def expected():return dict(containerId=CID,containerName='/roadmap-v17-'+'c'*32,initPid=10,initStarttime=500,cgroup=GROUP,leanSha256=SHA,lockDevice=1,lockInode=9)
def sample():return dict(rssBytes=100,leanWorkers=0,leanSupervisors=1,leanZombies=0,leanTransitions=0,unclassifiedLeanWorkers=1,unknownLeanProcesses=[dict(pid=123,state='R',rssBytes=0,arguments='[lean]')])
class IdentityTests(unittest.TestCase):
 def check(self,x=None,e=None):return m.check_worker(x or observation(),e or expected(),100*10**9,os.sysconf('SC_CLK_TCK'))
 def test_positive_consistency_only(self):self.assertEqual(self.check()['pid'],123)
 def test_mutations_fail_closed(self):
  mutations=[('afterStat',stat_text(123,1001)),('afterStat',stat_text(123,state='Z')),('beforeStat',stat_text(124)),('beforeStat','truncated'),('afterCgroup','0::/other'),('executableSha256','d'*64),('serializerLock',None),('serializerLock',dict(target=m.LOCK,device=1,inode=10)),('beginBootNs',1),('kernelValidated',True)]
  for key,value in mutations:
   with self.subTest(key=key,value=value):
    x=observation();x[key]=value
    with self.assertRaises((ValueError,KeyError,TypeError)):self.check(x)
 def test_fd_identity_mutations(self):
  for key,value in [('inode',3),('size',0),('size',True),('size',-1),('mtimeNs',False)]:
   x=observation();x['executableAfter'][key]=value
   with self.subTest(key=key,value=value),self.assertRaises(ValueError):self.check(x)
 def test_bad_expected(self):
  for key,value in [('initPid',True),('lockDevice',True),('initStarttime',-1),('cgroup','/'),('containerId','x'),('leanSha256','unknown')]:
   e=expected();e[key]=value
   with self.subTest(key=key,value=value),self.assertRaises((ValueError,TypeError)):self.check(e=e)
 def test_birth_after_snapshot_or_tick_ambiguity(self):
  x=observation();start=100*os.sysconf('SC_CLK_TCK');x['beforeStat']=x['afterStat']=stat_text(123,start)
  with self.assertRaises(ValueError):self.check(x)
 def test_preserves_original_unknown_and_rss(self):
  raw=sample();before=copy.deepcopy(raw)
  with patch.object(m,'observe_process',return_value=observation()):out=enrich(raw)
  self.assertEqual(raw,before);self.assertEqual(out['rssBytes'],100);self.assertEqual(out['leanWorkers'],1);self.assertEqual(out['unclassifiedLeanWorkers'],0);self.assertEqual(out['rawUnknownLeanProcesses'],raw['unknownLeanProcesses']);self.assertTrue(out['processIdentityObservations'][0]['identified'])
 def test_missing_identity_remains_unknown(self):
  for error in [FileNotFoundError('gone'),PermissionError('denied'),ValueError('malformed')]:
   with patch.object(m,'observe_process',side_effect=error):out=enrich(sample())
   self.assertEqual(out['unclassifiedLeanWorkers'],1);self.assertEqual(out['unknownLeanProcesses'],sample()['unknownLeanProcesses']);self.assertFalse(out['processIdentityObservations'][0]['identified'])
 def test_wrong_binary_not_whitelisted_by_zero_rss(self):
  x=observation();x['executableSha256']='f'*64
  with patch.object(m,'observe_process',return_value=x):out=enrich(sample())
  self.assertEqual(out['leanWorkers'],0);self.assertEqual(out['unclassifiedLeanWorkers'],1)
 def test_parallel_not_clamped(self):
  raw=sample();raw['leanWorkers']=1
  with patch.object(m,'observe_process',return_value=observation()):out=enrich(raw)
  self.assertEqual(out['leanWorkers'],2)
 def test_invalid_original_fields(self):
  for key,value in [('rssBytes',True),('rssBytes',-1),('leanWorkers',False),('unclassifiedLeanWorkers',0)]:
   raw=sample();raw[key]=value
   with self.subTest(key=key,value=value),self.assertRaises(ValueError):enrich(raw)
 def test_duplicate_pid_rejected(self):
  raw=sample();raw['unknownLeanProcesses']*=2;raw['unclassifiedLeanWorkers']=2
  with self.assertRaises(ValueError):enrich(raw)
 def test_live_own_process_observation(self):
  x=m.observe_process(os.getpid());v=m.stable_observation(x)
  self.assertEqual(v['pid'],os.getpid());self.assertFalse(x['kernelValidated']);self.assertGreater(x['executableBefore']['size'],0)
 def test_exec_association_swap_even_with_pinned_old_fd(self):
  x=observation();x['executableAssociationAfter']['inode']=99
  with self.assertRaises(ValueError):self.check(x)
 def test_missing_reopened_executable(self):
  x=observation();del x['executableAssociationAfter']
  with self.assertRaises(KeyError):self.check(x)
 def test_post_only_identity_never_repairs_unknown(self):
  with patch.object(m,'observe_process',return_value=observation()):out=m.enrich_live_sample(sample(),expected(),100*10**9,100*10**9+1000,{})
  self.assertEqual(out['unclassifiedLeanWorkers'],1);self.assertEqual(out['leanWorkers'],0)
 def test_changed_executable_across_bracket(self):
  before=pre_observation();after=observation();after['executableBefore']['inode']=33;after['executableAfter']['inode']=33;after['executableAssociationAfter']['inode']=33
  with self.assertRaises(ValueError):m.check_bracket(before,after,expected(),100*10**9,100*10**9+1000,os.sysconf('SC_CLK_TCK'))
 def test_unbracketed_snapshot_rejected(self):
  before=observation();after=observation()
  with self.assertRaises(ValueError):m.check_bracket(before,after,expected(),100*10**9,100*10**9+1000,os.sysconf('SC_CLK_TCK'))
 def test_container_policy_bindings(self):
  info=dict(Id=CID,Name='/roadmap-v17-'+'c'*32,State=dict(Running=True,Pid=10),HostConfig=dict(Memory=12*1024**3,MemorySwap=12*1024**3,NanoCpus=10**9,NetworkMode='none'))
  init=observation(10);init['beforeStat']=init['afterStat']=stat_text(10,500)
  self.assertEqual(m.expected_container(info,init,SHA)['containerId'],CID)
  for field,value in [('Memory',True),('Memory',-1),('MemorySwap',-1),('NanoCpus',True),('NanoCpus',2*10**9),('NetworkMode','host')]:
   changed=copy.deepcopy(info);changed['HostConfig'][field]=value
   with self.subTest(field=field,value=value),self.assertRaises(ValueError):m.expected_container(changed,init,SHA)
 def test_historical_failure_is_not_repaired(self):
  fixture=json.loads((Path(__file__).parent/'process-unknown-fixture.json').read_text());raw=fixture['sample'];before=copy.deepcopy(raw)
  with patch.object(m,'observe_process',side_effect=FileNotFoundError('historical process gone')):out=m.enrich_live_sample(raw,expected(),100*10**9,100*10**9+1000,{})
  self.assertEqual(raw,before);self.assertEqual(out['unclassifiedLeanWorkers'],1);self.assertEqual(out['unknownLeanProcesses'],raw['unknownLeanProcesses']);self.assertEqual(fixture['historicalOverallExit'],125)
 def test_consistently_malformed_fd_metadata_rejected(self):
  for key,value in [('size',True),('size',-1),('device',False),('inode',0),('mtimeNs',False)]:
   x=observation()
   for field in ['executableBefore','executableAfter','executableAssociationAfter']:x[field][key]=value
   with self.subTest(key=key,value=value),self.assertRaises(ValueError):self.check(x)
 def test_observed_lock_bool_not_equal_to_integer(self):
  x=observation();x['serializerLock']['device']=True
  with self.assertRaises(ValueError):self.check(x)
 def test_v1_and_traversal_cgroup_rejected(self):
  for raw in ['1:memory:/docker/'+CID,'0::/../docker/'+CID,'0::/a\n0::/b']:
   with self.subTest(raw=raw),self.assertRaises(ValueError):m.parse_cgroup(raw)
if __name__=='__main__':unittest.main()
