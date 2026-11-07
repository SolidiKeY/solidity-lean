#!/usr/bin/env python3
"""Guard H127 foreign-ID cleanup, ambiguous start and fake drain regressions.

Fake Docker cases test controller decisions, not containment. Real subprocess
cases test only bounded local-client transport. No Docker or Lean is executed.
"""
import copy
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

spec=importlib.util.spec_from_file_location('probe',Path(__file__).with_name('docker-probe.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
CID='c'*64
IMAGE='sha256:'+'d'*64
IDENTITY={'name':'h127-'+'a'*32,'nonce':'a'*32,'planSha256':'b'*64,'imageId':IMAGE}


def record(identity=IDENTITY,cpu=0):
    return {'Id':CID,'Name':'/'+identity['name'],'Image':identity['imageId'],
        'Config':{'Labels':m.labels(identity),'User':'1000:1000','Entrypoint':['/bin/sh'],
                  'Cmd':m.COMMAND.copy(),'WorkingDir':'/'},
        'HostConfig':{'ReadonlyRootfs':True,'Privileged':False,'NetworkMode':'none',
            'PidMode':'','IpcMode':'private','CgroupnsMode':'private',
            'Memory':m.MEMORY,'MemorySwap':m.MEMORY,'NanoCpus':10**9,'CpusetCpus':str(cpu),
            'PidsLimit':64,'CapDrop':['ALL'],'CapAdd':None,'SecurityOpt':['no-new-privileges'],
            'Binds':None,'Devices':None,'DeviceRequests':None,'RestartPolicy':{'Name':'no','MaximumRetryCount':0},
            'AutoRemove':False,'PortBindings':{},'Links':None,'VolumesFrom':None},'Mounts':[],
        'State':{'Running':True,'Pid':777,'Restarting':False,'ExitCode':0,'OOMKilled':False,'Status':'running'}}


class Fake:
    def __init__(self,identity=IDENTITY):
        self.data=record(identity);self.calls=[];self.gone=False
        self.binary='synthetic';self.socket={};self.daemon=[];self.trace=[]
    def inspect(self,cid):
        self.calls.append(('inspect',cid))
        if self.gone: raise m.ProbeError('missing container')
        return copy.deepcopy(self.data)
    def call(self,args):
        self.calls.append(tuple(args))
        if args[:2]==['container','kill']:
            self.data['State'].update(Running=False,Pid=0,ExitCode=137,Status='exited')
        elif args[:2]==['container','rm']:self.gone=True
        return b''
    def listed(self,filter_value):return []


class Pin:
    def __init__(self,*args):
        self.before={'synthetic':True,'path':'/synthetic'};self.observation={'synthetic':True};self.chain=[('',-1)]
    def removed(self):return {'removed':True,'synthetic':True}
    def close(self):pass


class DummyMonitor:
    def check(self):pass
    def add(self,*args):pass
    def stop(self):pass
    def finish(self):self.check()
    def summary(self):return {'synthetic':True}


class Controls(unittest.TestCase):
    def test_global_reservation_cannot_be_bypassed_by_new_destination(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'reservation.json'
            with patch.object(m,'RESERVATION',path):
                m.reserve_probe(Path(temp)/'first')
                with self.assertRaises(FileExistsError):m.reserve_probe(Path(temp)/'second')
            self.assertEqual(json.loads(path.read_text())['destination'],str(Path(temp)/'first'))

    def test_exact_recipe_has_no_mount_or_arbitrary_worker(self):
        args=m.create_args(IDENTITY,0)
        self.assertEqual(args[-3:],[IMAGE,'-c','exec /bin/sleep 60'])
        for flag in ('--pull=never','--network=none','--read-only','--cpuset-cpus=0','--memory-swap='+str(m.MEMORY)):
            self.assertIn(flag,args)
        self.assertFalse(any(x.startswith(('--mount','--volume','--privileged','--pid=')) for x in args))
        for bad in ('short','../id','C'*64):
            with self.assertRaises(m.ProbeError):m.exact_hex(bad)
        with self.assertRaises(m.ProbeError):m.create_args(IDENTITY,True)

    def test_ownership_requires_name_nonce_plan_image_and_full_id(self):
        for key in ('Name','Image','Id'):
            data=record();data[key]='foreign'
            with self.assertRaises(m.ProbeError):m.ownership(data,IDENTITY,CID)
        for key in m.labels(IDENTITY):
            data=record();data['Config']['Labels'][key]='foreign'
            with self.assertRaises(m.ProbeError):m.ownership(data,IDENTITY,CID)

    def test_policy_mutations_refused(self):
        m.policy(record(),IDENTITY,CID,0)
        for key,value in [('ReadonlyRootfs',False),('Privileged',True),('MemorySwap',-1),
                          ('NetworkMode','host'),('CpusetCpus','0-4'),('Binds',['/var/run/docker.sock:/socket'])]:
            data=record();data['HostConfig'][key]=value
            with self.assertRaises(m.ProbeError):m.policy(data,IDENTITY,CID,0)
        data=record();data['Config']['Cmd']=['arbitrary']
        with self.assertRaises(m.ProbeError):m.policy(data,IDENTITY,CID,0)

    def test_foreign_container_never_killed_or_removed(self):
        client=Fake();client.data['Config']['Labels'][m.LABEL+'nonce']='foreign'
        with self.assertRaises(m.ProbeError):m.cleanup(client,IDENTITY,CID,Pin())
        self.assertFalse(any(c[0]=='container' for c in client.calls))

    def test_owner_drift_between_inspections_prevents_kill(self):
        client=Fake();original=client.inspect
        def changing(cid):
            value=original(cid)
            if len(client.calls)>1:value['Name']='/foreign'
            return value
        client.inspect=changing
        with self.assertRaises(m.ProbeError):m.cleanup(client,IDENTITY,CID,Pin())
        self.assertFalse(any(c[0]=='container' for c in client.calls))

    def test_cleanup_requires_docker_absence_and_pinned_removal(self):
        client=Fake();result=m.cleanup(client,IDENTITY,CID,Pin())
        self.assertTrue(result['dockerIdAbsent']);self.assertEqual(result['exit']['ExitCode'],137)
        self.assertIn(('container','kill','--signal=KILL',CID),client.calls)
        self.assertIn(('container','rm',CID),client.calls)
        client=Fake()
        with self.assertRaisesRegex(m.ProbeError,'kernel drain pin'):m.cleanup(client,IDENTITY,CID,None)
        self.assertTrue(client.gone)
        client=Fake();client.listed=lambda x:[CID]
        with self.assertRaisesRegex(m.ProbeError,'persists'):m.cleanup(client,IDENTITY,CID,Pin())
        client=Fake();pin=Pin();pin.removed=lambda:{'removed':False}
        with self.assertRaisesRegex(m.ProbeError,'global deadline expired'):m.cleanup(client,IDENTITY,CID,pin,timeout=0)

    def test_client_failures_never_mean_container_absent(self):
        client=Fake()
        client.call=lambda args:(_ for _ in ()).throw(m.ProbeError('offline'))
        with self.assertRaisesRegex(m.ProbeError,'offline'):m.cleanup(client,IDENTITY,CID,Pin())
        self.assertFalse(client.gone)

    def test_bounded_transport_nonzero_timeout_and_output_limit(self):
        result=m.bounded([sys.executable,'-c','import sys;sys.stderr.write("error");sys.exit(7)'],{},timeout=2)
        self.assertEqual(result['code'],7);self.assertEqual(result['stderr'],b'error')
        with self.assertRaisesRegex(m.ProbeError,'timeout'):
            m.bounded([sys.executable,'-c','import time;time.sleep(3)'],{},timeout=0.02)
        with self.assertRaisesRegex(m.ProbeError,'output bound'):
            m.bounded([sys.executable,'-c','print("x"*10000)'],{},maximum=64)

    def test_ambiguous_create_reconciliation_never_infers_absence(self):
        client=Fake();client.listed=lambda key:[CID]
        self.assertEqual(m.reconcile(client,IDENTITY),CID)
        self.assertIsNone(client.guard)
        client.listed=lambda key:[]
        with self.assertRaisesRegex(m.ProbeError,'reconciliation unresolved'):m.reconcile(client,IDENTITY)
        client.listed=lambda key:[CID,CID]
        with self.assertRaisesRegex(m.ProbeError,'reconciliation unresolved'):m.reconcile(client,IDENTITY)
        client.listed=lambda key:[CID];client.data['Name']='/foreign'
        with self.assertRaisesRegex(m.ProbeError,'foreign'):m.reconcile(client,IDENTITY)

    def test_cleanup_uses_one_deadline_for_all_calls(self):
        client=Fake();pin=Pin()
        with self.assertRaisesRegex(m.ProbeError,'global deadline expired'):
            m.cleanup(client,IDENTITY,CID,pin,timeout=0)
        self.assertIsNone(client.guard)
        self.assertIsInstance(client.deadline,int)

    def test_reserve_sampling_breach_and_drift_are_fatal(self):
        import threading
        guard=object.__new__(m.ReserveMonitor)
        guard.lock=threading.RLock();guard.samples=[];guard.failure=None;guard.minimum=None
        guard.entries=[{'fd':123,'path':'/outer','identity':{'inode':9},'constraints':{'memoryMaxBytes':16*1024**3},'worker':False,'removed':False}]
        good={'memoryMaxBytes':16*1024**3}
        with patch.object(m.resources,'constraints',return_value=good),patch.object(m.resources,'_identity',return_value={'inode':9}),patch.object(m.os,'fstat',return_value=type('Stat',(),{'st_nlink':1})()),patch.object(m.resources,'_read',return_value=str(13*1024**3)):
            with self.assertRaisesRegex(m.ProbeError,'reserve breached'):guard.sample()
            self.assertEqual(guard.minimum,3*1024**3)
            self.assertEqual(guard.samples[0]['groups'][0]['availableBytes'],3*1024**3)
        with patch.object(m.resources,'constraints',return_value={'memoryMaxBytes':15*1024**3}),patch.object(m.os,'fstat',return_value=type('Stat',(),{'st_nlink':1})()):
            with self.assertRaisesRegex(m.ProbeError,'constraints or identity'):guard.sample()
        guard.failure='retained fatal breach'
        with self.assertRaisesRegex(m.ProbeError,'retained fatal'):guard.check()

    def test_transport_guard_triggers_and_child_reaper_refused(self):
        def breach():raise m.ProbeError('reserve breach')
        with self.assertRaisesRegex(m.ProbeError,'reserve breach'):
            m.bounded([sys.executable,'-c','import time;time.sleep(3)'],{},guard=breach)
        with patch.object(m.signal,'getsignal',return_value=m.signal.SIG_IGN):
            with self.assertRaisesRegex(m.ProbeError,'child reaper'):
                m.bounded([sys.executable,'-c','pass'],{})

    def synthetic_probe(self,mode):
        class ControllerFake(Fake):
            def __init__(self):super().__init__();self.created=False
            def call(self,args):
                if args[:2]==['container','create']:
                    self.created=True
                    name=args[args.index('--name')+1]
                    identity={'name':name,'nonce':name[5:],'planSha256':None,'imageId':IMAGE}
                    for item in args:
                        if item.startswith(m.LABEL+'plan='):identity['planSha256']=item.split('=',1)[1]
                    self.data=record(identity,min(os.sched_getaffinity(0)))
                    self.data['State'].update(Running=False,Pid=0,Status='created')
                    if mode=='policy':self.data['HostConfig']['Privileged']=True
                    if mode=='create':raise m.ProbeError('create interrupted')
                    return (CID+'\n').encode()
                if args[:2]==['container','start']:
                    if mode=='start':raise m.ProbeError('start interrupted')
                    self.data['State'].update(Running=True,Pid=777,Status='running')
                return super().call(args)
        client=ControllerFake()
        class LateMonitor(DummyMonitor):
            def finish(self):raise m.ProbeError('fatal monitor failure during finalization')
        monitor_type=LateMonitor if mode=='late-monitor' else DummyMonitor
        own={'ancestors':[{'constraints':{'memoryMaxBytes':16*1024**3},'memoryCurrentBytes':1024}]}
        with tempfile.TemporaryDirectory() as temp:
            dest=Path(temp)/'probe'
            with patch.object(m,'Docker',return_value=client),patch.object(m.resources,'observe',return_value=own),patch.object(m,'PinnedGroup',Pin),patch.object(m,'ReserveMonitor',monitor_type):
                result=m.probe(dest,IMAGE)
            locator=json.loads((dest/'locator.json').read_text())
            with m.journal_module.Journal(dest/'state',locator) as journal:
                active=journal.read_active()
                with self.assertRaises(m.journal_module.Unresolved):journal.reserve('e'*64,IMAGE)
                with self.assertRaises(m.journal_module.Unresolved):journal.seal_pre_create_abort()
            self.assertFalse(result['measurementAccepted']);self.assertFalse(result['postCreateBarrierReleased'])
            return result,client,active

    def test_synthetic_success_retains_post_create_barrier(self):
        result,client,active=self.synthetic_probe('success')
        self.assertEqual(result['status'],'probe-drain-observed')
        self.assertEqual(active['events'][-1]['state'],'drain-observed')
        self.assertTrue(client.gone)

    def test_late_monitor_failure_never_publishes_positive_drain(self):
        result,client,active=self.synthetic_probe('late-monitor')
        self.assertTrue(client.gone)
        self.assertIn('cleanup',result)
        self.assertEqual(result['status'],'unresolved')
        self.assertEqual(active['events'][-1]['state'],'cleanup-unresolved')
        self.assertIn('fatal monitor',result['error'])

    def test_ambiguous_create_start_and_bad_policy_never_advance_worker(self):
        for mode in ('create','start','policy'):
            result,client,active=self.synthetic_probe(mode)
            self.assertEqual(result['status'],'unresolved')
            self.assertEqual(active['events'][-1]['state'],'cleanup-unresolved')
            if mode in ('create','policy'):
                self.assertFalse(any(c[:2]==('container','start') for c in client.calls))


if __name__=='__main__':unittest.main()
