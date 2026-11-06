#!/usr/bin/env python3
"""Synthetic consistency controls; no Docker/native proof execution."""
import copy
import json
import os
from pathlib import Path
import resource
import types
import unittest
from unittest.mock import patch
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(60,)*2)
ROOT=Path(__file__).resolve().parents[2]
def load(name,path):
    m=types.ModuleType(name);m.__file__=str(path);exec(compile(path.read_bytes(),str(path),'exec'),m.__dict__);return m
old=load('fixtures',Path(__file__).with_name('test_process_identity.py'))
m=old.m
t=load('transport',ROOT/'scripts/roadmap-v17-container-identity.py')
CID=old.CID

def public(pid,inner,start=1000):
    return dict(pid=pid,observerTimeNamespaceBefore='time:[789]',observerTimeNamespaceAfter='time:[789]',beforeTimeNamespace='time:[789]',afterTimeNamespace='time:[789]',beginBootNs=1,endBootNs=2,beforeStat=old.stat_text(pid,start),afterStat=old.stat_text(pid,start),beforeCgroup='0::'+old.GROUP,afterCgroup='0::'+old.GROUP,beforeStatus=f'NSpid: {pid} {inner}\n',afterStatus=f'NSpid: {pid} {inner}\n')
def inner(pid,start=1000):
    out=old.observation(pid);out['beforeStat']=out['afterStat']=old.stat_text(pid,start)
    out['beforeCgroup']=out['afterCgroup']='0::/';return out

def fixture():
    req=dict(schema=1,nonce='d'*32,containerId=CID,observerSha256=t.digest((ROOT/'scripts/roadmap-v17-process-identity.py').read_bytes()),transportSha256=t.digest(Path(t.__file__).read_bytes()),pids=[2],binding=dict(consumerHead='e'*40,sourceToolchainKey='f'*64))
    ns=dict(pid='pid:[123]',cgroup='cgroup:[456]',time='time:[789]')
    reply=dict(schema=1,requestSha256=t.digest(t.canonical(req)),**{k:req[k] for k in ['nonce','containerId','observerSha256','transportSha256','binding']},actorUid=0,initBefore=inner(1,500),initAfter=inner(1,500),pidNamespace=ns['pid'],cgroupNamespace=ns['cgroup'],timeNamespace=ns['time'],initTimeNamespaceAfter=ns['time'],observerTimeNamespaceAfter=ns['time'],observedCaps={'memory.max':'12884901888','memory.swap.max':'0','cpu.max':'100000 100000'},rows=[dict(pid=2,outcome='observed',observation=inner(2),namespacesBefore=ns.copy(),namespacesAfter=ns.copy())],**t.FLAGS)
    info=dict(Id=CID,Name='/roadmap-v17-'+'c'*32,State=dict(Running=True,Pid=10),HostConfig=dict(Memory=12*1024**3,MemorySwap=12*1024**3,NanoCpus=10**9,NetworkMode='none'))
    reply['initBefore'].update(beginBootNs=10,endBootNs=11);reply['rows'][0]['observation'].update(beginBootNs=20,endBootNs=21);reply['initAfter'].update(beginBootNs=30,endBootNs=31)
    last_init=public(10,1,500);last_init.update(beginBootNs=50,endBootNs=51)
    last_worker=public(123,2);last_worker.update(beginBootNs=40,endBootNs=41)
    return [req,reply,info,public(10,1,500),last_init,{2:public(123,2)},{2:last_worker}]
def verify(x):return t.validate_reply(m,*x)
class TransportTests(unittest.TestCase):
 def test_positive_synthetic_nonpromotion(self):
    out=verify(fixture());self.assertTrue(out['consistencyOnly']);self.assertFalse(out['liveTransportAuthenticated']);self.assertFalse(out['kernelValidated']);self.assertFalse(out['releaseClosed']);self.assertEqual(out['bindings'][0]['hostPid'],123)
 def test_request_identity_mutations(self):
    for field,value in [('nonce','0'*32),('containerId','0'*64),('observerSha256','0'*64),('transportSha256','0'*64),('binding',dict(consumerHead='0'*40,sourceToolchainKey='0'*64))]:
     x=fixture();x[1][field]=value
     with self.subTest(field=field),self.assertRaises((ValueError,KeyError,TypeError)):verify(x)
 def test_bad_requests(self):
    for field,value in [('schema',True),('pids',[True]),('pids',[]),('pids',[2,2]),('nonce','x'),('binding',{})]:
     x=fixture();x[0][field]=value
     with self.subTest(field=field,value=value),self.assertRaises((ValueError,KeyError,TypeError)):verify(x)
 def test_reply_omission_duplicate_boolean_and_failure(self):
    for rows in [[],[dict(pid=True)],[dict(pid=2,outcome='unavailable')],fixture()[1]['rows']*2]:
     x=fixture();x[1]['rows']=rows
     with self.subTest(rows=rows),self.assertRaises((ValueError,KeyError,TypeError)):verify(x)
 def test_caps_and_policy(self):
    for field,value in [('Memory',True),('MemorySwap',-1),('NanoCpus',2*10**9),('NetworkMode','host')]:
     x=fixture();x[2]['HostConfig'][field]=value
     with self.subTest(field=field),self.assertRaises(ValueError):verify(x)
    for field in ['memory.max','memory.swap.max','cpu.max']:
     x=fixture();x[1]['observedCaps'][field]='max'
     with self.subTest(field=field),self.assertRaises(ValueError):verify(x)
 def test_namespace_and_host_mapping(self):
    for index,field,value in [(4,'afterStat',old.stat_text(10,501)),(6,None,None),(3,'beforeCgroup','0::/'),(5,None,None)]:
     x=fixture()
     if index==6:x[index][2]['afterStatus']='NSpid: 123 3'
     elif index==5:x[index][2]['beforeCgroup']=x[index][2]['afterCgroup']='0::/elsewhere'
     else:x[index][field]=value
     with self.subTest(index=index),self.assertRaises(ValueError):verify(x)
 def test_inner_exec_reuse_namespace_and_source_mutations(self):
    for field,value in [('namespacesAfter',dict(pid='pid:[789]',cgroup='cgroup:[456]')),('observation',inner(3))]:
     x=fixture();x[1]['rows'][0][field]=value
     with self.subTest(field=field),self.assertRaises(ValueError):verify(x)
    x=fixture();x[1]['rows'][0]['observation']['executableAssociationAfter']['inode']=99
    with self.assertRaises(ValueError):verify(x)
    with self.assertRaises(ValueError):t.load_observer('0'*64)
 def test_promoted_or_truncated_reply(self):
    for key in t.FLAGS:
     x=fixture();x[1][key]=True
     with self.subTest(key=key),self.assertRaises(ValueError):verify(x)
    x=fixture();del x[1]['initAfter']
    with self.assertRaises(KeyError):verify(x)
 def test_stale_and_out_of_window_clocks(self):
    for where,begin,end in [('row',0,1),('row',32,33),('init',0,1),('outer',False,2),('outer',3,2)]:
     x=fixture();v=x[1]['rows'][0]['observation'] if where=='row' else x[1]['initBefore'] if where=='init' else x[3]
     v.update(beginBootNs=begin,endBootNs=end)
     with self.subTest(where=where,begin=begin),self.assertRaises(ValueError):verify(x)
 def test_clock_namespace_mutations(self):
    for where in ['reply','public','worker','observer','inner-observer']:
     x=fixture()
     if where=='reply':x[1]['timeNamespace']='time:[999]'
     elif where=='public':x[3]['beforeTimeNamespace']='time:[999]'
     elif where=='observer':x[3]['observerTimeNamespaceBefore']=x[3]['observerTimeNamespaceAfter']='time:[999]'
     elif where=='inner-observer':x[1]['observerTimeNamespaceAfter']='time:[999]'
     else:x[5][2]['beforeTimeNamespace']=x[5][2]['afterTimeNamespace']='time:[999]'
     with self.subTest(where=where),self.assertRaises(ValueError):verify(x)
 def test_duplicate_json_rejected(self):
    with self.assertRaises(ValueError):json.loads('{"schema":1,"schema":1}',object_pairs_hook=t.unique_object)
 def test_actual_own_public_mapping_only(self):
    try:out=t.public_process(m,os.getpid())
    except FileNotFoundError as error:
     self.assertEqual(error.filename,'/proc/'+str(os.getpid())+'/ns/time')
     return  # Unsupported real platform is NONPASS, not synthetic transport evidence.
    self.assertEqual(t.stable_public(m,out)['pid'],os.getpid())
 def test_preflight_source_failure_launches_no_observation(self):
    req=fixture()[0];req['transportSha256']='0'*64
    with patch.object(t,'load_observer') as observer:
     with self.assertRaises(ValueError):t.inside_observations(req)
     observer.assert_not_called()
 def test_old_root_cgroup_fence_unchanged(self):
    e=old.expected();e['cgroup']='/'
    with self.assertRaises(ValueError):m.validate_expected(e)
if __name__=='__main__':unittest.main()
