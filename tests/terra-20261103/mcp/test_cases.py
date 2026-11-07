"""Guard MCP daemon death after disconnects, duplicate servers and false successes.

The real pinned wrapper and Unix sockets run against a recording JSON-RPC server.
No Lean process runs; successful mock responses establish protocol behavior only.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import signal
import socket
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[3]
TOOL = ROOT / 'scripts/coord-tools/lean-mcp'
TOOLS = ['echo', 'lean_diagnostic_messages', 'lean_goal', 'lean_multi_attempt']
SERVER = r'''import json, os, pathlib, sys, time
for raw in sys.stdin:
    msg=json.loads(raw)
    with open(os.environ['FIXTURE_RECORD'],'a') as f:
        f.write(json.dumps({'pid':os.getpid(),'cwd':os.getcwd(),'message':msg})+'\n')
    cfg=json.loads(pathlib.Path(os.environ['FIXTURE_CONFIG']).read_text())
    method=msg['method']
    if 'id' not in msg: continue
    if method=='initialize': result={}
    elif method=='tools/list':
        result={'tools':[{'name':n} for n in ['echo','lean_diagnostic_messages','lean_goal','lean_multi_attempt']]}
    elif method=='tools/call':
        name=msg['params']['name']; args=msg['params']['arguments']
        if name=='die': sys.exit(7)
        if name=='hold':
            pathlib.Path(os.environ['FIXTURE_ENTERED']).write_text('entered')
            deadline=time.monotonic()+25
            while not pathlib.Path(os.environ['FIXTURE_RELEASE']).exists():
                if time.monotonic()>deadline: sys.exit(8)
                time.sleep(.01)
        if cfg.get('rpc_error'):
            print(json.dumps({'jsonrpc':'2.0','id':msg['id'],'error':{'code':-32000,'message':'fixture rpc error'}}),flush=True)
            continue
        if cfg.get('tool_error'):
            result={'isError':True,'content':[{'type':'text','text':'fixture tool error'}]}
        elif name=='lean_diagnostic_messages':
            data={'items':cfg.get('items',[])}
            result={'structuredContent':{'result':data}}
        elif name=='lean_goal':
            result={'content':[{'type':'text','text':json.dumps({'goals':['⊢ True']})}]}
        elif name=='lean_multi_attempt':
            items=[]
            for snippet in args['snippets']:
                item={'snippet':snippet,'goals':[],'diagnostics':[]}
                if snippet=='goal': item['goals']=['⊢ False']
                elif snippet=='error': item['diagnostics']=[{'severity':'error','message':'rejected'}]
                elif snippet=='timeout': item['timed_out']=True
                items.append(item)
            data={'items':items}
            data.update({k:cfg[k] for k in ('partial','timed_out') if k in cfg})
            result={'structuredContent':data}
        else: result={'content':[{'type':'text','text':json.dumps(args,sort_keys=True)}]}
    else: raise RuntimeError('unexpected method '+method)
    print(json.dumps({'jsonrpc':'2.0','id':msg['id'],'result':result}),flush=True)
'''


class MCP(unittest.TestCase):
    def setUp(self):
        # A short private socket directory stays below AF_UNIX's path limit.
        self.tmp = tempfile.TemporaryDirectory(prefix='mcpf-')
        self.base = Path(self.tmp.name)
        self.repo = self.base / 'repo one'; self.repo.mkdir()
        self.other = self.base / 'repo two'; self.other.mkdir()
        self.home = self.base / 'home'; self.home.mkdir()
        self.socks = self.base / 's'; self.socks.mkdir()
        self.scratch = self.base / 'tmp'; self.scratch.mkdir()
        self.record = self.base / 'rpc.jsonl'
        self.config = self.base / 'config.json'; self.config.write_text('{}')
        self.entered = self.base / 'entered'; self.release = self.base / 'release'
        self.mock = self.base / 'mock server.py'; self.mock.write_text(SERVER)
        self.wrapper = self.base / 'lean-mcp'; self.wrapper.write_bytes(TOOL.read_bytes())
        self.assertEqual(hashlib.sha256(self.wrapper.read_bytes()).hexdigest(),
                         '277a9b9675cea5d32ee1f3bf296f550ad1220574313accad3143006aa5d07222')
        self.env = {'PATH':os.path.dirname(sys.executable) + os.pathsep + '/usr/bin:/bin',
                    'HOME':str(self.home), 'TMPDIR':str(self.scratch),
                    'PYTHONDONTWRITEBYTECODE':'1',
                    'LEAN_MCP_SOCKDIR':str(self.socks),
                    'LEAN_MCP_SERVER_CMD':shlex.join([sys.executable,str(self.mock)]),
                    'LEAN_MCP_START_WAIT':'5', 'LEAN_MCP_TIMEOUT':'20', 'LEAN_MCP_IDLE':'60',
                    'FIXTURE_RECORD':str(self.record), 'FIXTURE_CONFIG':str(self.config),
                    'FIXTURE_ENTERED':str(self.entered), 'FIXTURE_RELEASE':str(self.release)}
        self.clients = []; self.invocations = []; self.owned = {}
        self.addCleanup(self.cleanup)
        for repo in (self.repo,self.other):
            subprocess.run(['git','init','-q',str(repo)],env=self.env,check=True)

    def process_identity(self, pid):
        try:
            proc = Path('/proc') / str(pid)
            self.assertEqual(proc.stat().st_uid,os.getuid())
            fields = (proc/'stat').read_text().rpartition(')')[2].split()
            argv = (proc/'cmdline').read_bytes().split(b'\0')
            return {'state':fields[0],'parent':int(fields[1]),'start':fields[19],
                    'argv':[os.fsdecode(a) for a in argv if a]}
        except (FileNotFoundError,ProcessLookupError): return None

    def own(self, pid, kind, repo):
        identity = self.process_identity(pid)
        self.assertIsNotNone(identity)
        expected = ([str(self.wrapper),'--daemon',str(repo.resolve()),str(self.sock(repo))]
                    if kind=='daemon' else [str(self.mock)])
        self.assertEqual(identity['argv'][1:],expected)
        self.owned[pid] = {'start':identity['start'],'argv':identity['argv'],
                           'kind':kind,'repo':str(repo)}

    def alive(self, pid):
        identity = self.process_identity(pid)
        return bool(identity and identity['start']==self.owned[pid]['start']
                    and identity['state']!='Z')

    def assert_stopped(self, ids):
        self.wait_for(lambda:all(not self.alive(pid) for pid in ids))

    def check_stop_result(self, result):
        self.assertEqual((result.returncode,result.stdout,result.stderr),(0,'',''))

    def stop_and_wait(self, repo=None):
        repo = repo or self.repo
        result = self.run_cli('stop',repo=repo)
        self.check_stop_result(result)
        self.wait_for(lambda:not self.sock(repo).exists())
        self.assert_stopped([pid for pid,data in self.owned.items() if data['repo']==str(repo)])

    def recover_owned(self):
        # A failed concurrent-start assertion may precede start()'s PID capture.
        # Recover only identities recorded by this fixture's private fake server.
        for row in self.records():
            pid = row['pid']; repo = Path(row['cwd'])
            self.assertIn(repo,(self.repo,self.other))
            identity = self.process_identity(pid)
            if not identity or identity['state']=='Z': continue
            self.own(pid,'server',repo)
            parent = identity['parent']; parent_identity = self.process_identity(parent)
            if parent_identity and parent_identity['argv'][1:]==[
                    str(self.wrapper),'--daemon',str(repo.resolve()),str(self.sock(repo))]:
                self.own(parent,'daemon',repo)

    def cleanup(self):
        failure = None
        self.release.touch()
        try:
            for proc in self.clients:
                if proc.poll() is None: proc.communicate(timeout=5)
            self.recover_owned()
            for repo in (self.repo,self.other):
                if self.sock(repo).exists(): self.stop_and_wait(repo)
            self.assert_stopped(self.owned)
        except BaseException as exc: failure = exc
        finally:
            # Failure cleanup is identity-bound, never pkill or a host daemon stop.
            for sig in (signal.SIGTERM,signal.SIGKILL):
                for pid,data in self.owned.items():
                    identity = self.process_identity(pid)
                    if self.alive(pid) and identity['argv']==data['argv']:
                        os.kill(pid,sig)
                deadline = time.monotonic()+2
                while time.monotonic()<deadline and any(self.alive(pid) for pid in self.owned):
                    time.sleep(.01)
            for proc in self.clients:
                if proc.poll() is None: proc.terminate(); proc.communicate(timeout=5)
            evidence = os.environ.get('TF_MCP_EVIDENCE')
            if evidence:
                out = Path(evidence); out.mkdir(parents=True,exist_ok=True)
                (out/(self.id().rsplit('.',1)[-1]+'.json')).write_text(json.dumps(
                    {'invocations':self.invocations,'rpc':self.records(),
                     'owned_processes':self.owned,'cleanup_failure':str(failure) if failure else None,
                     'alive_after_cleanup':[pid for pid in self.owned if self.alive(pid)]},indent=2)+'\n')
            self.tmp.cleanup()
        if failure is not None: raise failure

    def sock(self, repo=None):
        root = str((repo or self.repo).resolve())
        return self.socks / ('lean-mcp-'+hashlib.sha256(root.encode()).hexdigest()[:20]+'.sock')

    def run_cli(self, *args, repo=None, rc=0, timeout=16):
        proc = subprocess.run([sys.executable,str(self.wrapper),*map(str,args)],
                              cwd=repo or self.repo,env=self.env,
                              capture_output=True,text=True,timeout=timeout)
        self.invocations.append({'args':list(map(str,args)), 'repo':str(repo or self.repo),
                                 'exit':proc.returncode,'stdout':proc.stdout,'stderr':proc.stderr})
        self.assertEqual(proc.returncode,rc,proc.stderr+proc.stdout)
        return proc

    def start(self, repo=None):
        self.run_cli('start',repo=repo)
        status = self.run_cli('status',repo=repo)
        match = re.fullmatch(r'pid=(\d+) server=(\d+) socket=(.+)\n',status.stdout)
        self.assertIsNotNone(match,status.stdout)
        self.assertEqual(match[3],str(self.sock(repo)))
        self.assertEqual(self.sock(repo).stat().st_mode & 0o777,0o600)
        daemon,server = int(match[1]),int(match[2])
        self.own(daemon,'daemon',repo or self.repo)
        self.own(server,'server',repo or self.repo)
        self.assertTrue(any(r['pid']==server and r['cwd']==str((repo or self.repo).resolve())
                            for r in self.records()))
        return daemon,server

    def records(self):
        return [json.loads(s) for s in self.record.read_text().splitlines()] if self.record.exists() else []

    def check_rpc(self, groups):
        # Enumerate every request, including startup notifications, not a sampled subset.
        actual = {}
        for row in self.records(): actual.setdefault(row['pid'],[]).append(row)
        self.assertEqual(len(actual),len(groups))
        for rows,(repo,calls) in zip(actual.values(),groups):
            self.assertTrue(all(r['cwd']==str(repo.resolve()) for r in rows))
            init = {'protocolVersion':'2025-06-18','capabilities':{},
                    'clientInfo':{'name':'coord-tools','version':'1'}}
            expected = [('initialize',init),('notifications/initialized',{})]+calls
            self.assertEqual(len(rows),len(expected))
            seq = 0
            for row,(method,params) in zip(rows,expected):
                msg = row['message']
                if method=='notifications/initialized':
                    self.assertEqual(msg,{'jsonrpc':'2.0','method':method,'params':params})
                else:
                    seq += 1
                    self.assertEqual(msg,{'jsonrpc':'2.0','method':method,'params':params,'id':seq})

    def call(self, name, arguments=None, **kwargs):
        return self.run_cli('call',name,json.dumps(arguments or {}),**kwargs)

    def wait_for(self, predicate, timeout=5):
        deadline = time.monotonic()+timeout
        while time.monotonic()<deadline:
            if predicate(): return
            time.sleep(.01)
        self.fail('bounded fixture condition did not become true')

    def async_hold(self):
        proc = subprocess.Popen([sys.executable,str(self.wrapper),'call','hold','{}'],
                                cwd=self.repo,env=self.env,stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE,text=True)
        self.clients.append(proc)
        self.wait_for(self.entered.exists)
        return proc

    def test_usage(self):
        for args in [(),('unknown',)]:
            p=self.run_cli(*args,rc=2)
            self.assertIn('lean-mcp:',p.stderr)
        self.assertFalse(self.sock().exists())
        self.assertEqual(self.records(),[])

    def test_start_status_stop(self):
        self.run_cli('status',rc=1)
        ids=self.start()
        self.assertGreater(ids[0],0); self.assertGreater(ids[1],0)
        p=self.run_cli('tools'); self.assertEqual(p.stdout.splitlines(),TOOLS)
        self.assertEqual(self.call('echo',{'key':'value'}).stdout,'{"key": "value"}\n')
        with self.assertRaises(AssertionError):
            self.check_stop_result(subprocess.CompletedProcess(['stop'],1,'','fixture failure'))
        self.stop_and_wait()
        self.run_cli('status',rc=1)
        self.assertEqual(set(self.socks.iterdir()),{Path(str(self.sock())+'.lock')})
        self.check_rpc([(self.repo,[('tools/list',{}),('tools/call',{'name':'echo','arguments':{'key':'value'}})])])

    def test_same_checkout_single_daemon(self):
        processes=[subprocess.Popen([sys.executable,str(self.wrapper),'start'],cwd=self.repo,
                                   env=self.env,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
                   for _ in range(3)]
        self.clients.extend(processes)
        for p in processes:
            stdout,stderr=p.communicate(timeout=10); self.assertEqual(p.returncode,0,(stdout,stderr))
        first=self.start(); second=self.start(); self.assertEqual(first,second)
        self.assertEqual(len(list(self.socks.glob('*.sock'))),1)
        self.check_rpc([(self.repo,[])])

    def test_different_checkouts_isolated(self):
        first=self.start(); second=self.start(self.other)
        self.assertNotEqual(first[0],second[0]); self.assertNotEqual(first[1],second[1])
        self.assertNotEqual(self.sock(),self.sock(self.other))
        self.assertEqual(set(self.socks.glob('*.sock')),{self.sock(),self.sock(self.other)})
        self.stop_and_wait(self.other)
        self.assertEqual(self.start(),first)
        self.check_rpc([(self.repo,[]),(self.other,[])])

    def test_closed_probe_survives(self):
        ids=self.start()
        with socket.socket(socket.AF_UNIX) as s: s.connect(str(self.sock()))
        self.assertEqual(self.start(),ids)
        self.check_rpc([(self.repo,[])])

    def test_abandoned_client_survives(self):
        ids=self.start()
        with socket.socket(socket.AF_UNIX) as s:
            s.connect(str(self.sock()))
            s.sendall(b'{"kind":"call","name":"hold","arguments":{}}\n')
            self.wait_for(self.entered.exists)
        self.release.touch()
        self.assertEqual(self.start(),ids)
        self.check_rpc([(self.repo,[('tools/call',{'name':'hold','arguments':{}})])])

    def test_busy_status(self):
        ids=self.start(); proc=self.async_hold()
        try:
            p=self.run_cli('status',timeout=14)
            self.assertEqual(p.stdout,'busy socket='+str(self.sock())+'\n')
        finally: self.release.touch()
        stdout,stderr=proc.communicate(timeout=5)
        self.assertEqual((proc.returncode,stdout,stderr),(0,'{}\n',''))
        self.assertEqual(self.start(),ids)
        self.check_rpc([(self.repo,[('tools/call',{'name':'hold','arguments':{}})])])

    def test_tool_error(self):
        ids=self.start(); self.config.write_text('{"tool_error":true}')
        self.assertEqual(self.call('echo',rc=1).stdout,'fixture tool error\n')
        p=self.run_cli('diag','File.lean',rc=2); self.assertIn('MCP tool error',p.stderr)
        self.config.write_text('{"rpc_error":true}')
        p=self.call('echo',rc=2); self.assertIn('fixture rpc error',p.stderr)
        self.assertEqual(self.start(),ids)
        self.check_rpc([(self.repo,[('tools/call',{'name':'echo','arguments':{}}),
                                  ('tools/call',{'name':'lean_diagnostic_messages','arguments':{
                                      'file_path':str(self.repo/'File.lean'),'severity':'error','interactive':False}}),
                                  ('tools/call',{'name':'echo','arguments':{}})])])

    def test_diagnostic_error(self):
        self.start()
        items=[{'severity':'warning','line':1,'column':2,'message':'ignore'},
               {'severity':'error','line':3,'column':5,'message':'bad'}]
        self.config.write_text(json.dumps({'items':items}))
        p=self.run_cli('diag','File.lean',rc=1)
        self.assertEqual(p.stdout,'ERROR 3:5 bad\ndiag: 1 errors\n')
        self.config.write_text(json.dumps({'items':[items[0]]}))
        self.assertEqual(self.run_cli('diag','File.lean').stdout,'diag: 0 errors\n')
        self.config.write_text('{}')
        self.assertEqual(self.run_cli('diag','File.lean').stdout,'diag: 0 errors\n')
        call=('tools/call',{'name':'lean_diagnostic_messages','arguments':{
            'file_path':str(self.repo/'File.lean'),'severity':'error','interactive':False}})
        self.check_rpc([(self.repo,[call,call,call])])

    def test_server_death(self):
        first=self.start()
        p=self.call('die',rc=2); self.assertIn('MCP server exited',p.stderr)
        self.wait_for(lambda:not self.sock().exists())
        self.assert_stopped(first)
        second=self.start(); self.assertNotEqual(first[0],second[0]); self.assertNotEqual(first[1],second[1])
        self.assertEqual(self.run_cli('tools').stdout.splitlines(),TOOLS)
        self.check_rpc([(self.repo,[('tools/call',{'name':'die','arguments':{}})]),
                        (self.repo,[('tools/list',{})])])

    def test_idle_shutdown(self):
        self.env['LEAN_MCP_IDLE']='0.4'; ids=self.start()
        self.wait_for(lambda:not self.sock().exists())
        self.assert_stopped(ids)
        self.run_cli('status',rc=1)
        self.check_rpc([(self.repo,[])])

    def test_tactic_success(self):
        self.start(); snippets=['rfl','goal','omega']
        p=self.run_cli('try','File.lean','7',*snippets)
        self.assertEqual(p.stdout,'PASS rfl\nFAIL goal\nPASS omega\n')
        self.check_rpc([(self.repo,[('tools/call',{'name':'lean_multi_attempt','arguments':{
            'file_path':str(self.repo/'File.lean'),'line':7,'snippets':snippets}})])])

    def test_tactic_failure(self):
        self.start(); snippets=['goal','error','timeout']
        p=self.run_cli('try','File.lean','9',*snippets,rc=1)
        self.assertEqual(p.stdout,'FAIL goal\nFAIL error\nFAIL timeout\n')
        call=('tools/call',{'name':'lean_multi_attempt','arguments':{
            'file_path':str(self.repo/'File.lean'),'line':9,'snippets':snippets}})
        for flag in ('partial','timed_out'):
            self.config.write_text(json.dumps({flag:True}))
            p=self.run_cli('try','File.lean','9',*snippets,rc=2)
            self.assertIn('MCP response is incomplete',p.stderr); self.assertEqual(p.stdout,'')
        self.check_rpc([(self.repo,[call,call,call])])

    def test_invalid_json(self):
        ids=self.start()
        p=self.run_cli('call','echo','{',rc=2)
        self.assertIn('lean-mcp:',p.stderr)
        with socket.socket(socket.AF_UNIX) as s:
            s.settimeout(3); s.connect(str(self.sock())); s.sendall(b'{broken\n')
            reply=json.loads(s.makefile('rb').readline())
            self.assertFalse(reply['ok']); self.assertIsInstance(reply['error'],str)
            self.assertEqual(set(reply),{'ok','error'})
        self.assertEqual(self.start(),ids)
        self.check_rpc([(self.repo,[])])
