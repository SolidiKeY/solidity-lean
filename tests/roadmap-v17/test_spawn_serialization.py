"""Execute the production shell admission logic with tiny synthetic native jobs.
Only lock/tool prefix paths are substituted; no Lean proof or build is run.
"""
import importlib.util
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time
import unittest

ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('spawn_provenance',ROOT/'scripts/roadmap-v17-provenance.py')
p=importlib.util.module_from_spec(spec); spec.loader.exec_module(p)

WORKER = r'''#!/usr/bin/env python3
import json,os,subprocess,sys,time
from pathlib import Path
log=Path(os.environ['V17_TEST_EVENTS'])
def emit(phase):
    data=json.dumps({'phase':phase,'family':os.environ['V17_TEST_FAMILY'],'tool':Path(sys.argv[0]).name,'argv':sys.argv[1:]})+'\n'
    fd=os.open(log,os.O_CREAT|os.O_WRONLY|os.O_APPEND,0o600)
    os.write(fd,data.encode()); os.close(fd)
emit('enter')
role=sys.argv[-1]
code=0
if role.startswith('nested'):
    keep=(9,) if role=='nested' else ()
    code=subprocess.run([os.environ['V17_TEST_NESTED'],'leaf'],pass_fds=keep).returncode
else:
    time.sleep(float(os.environ.get('V17_TEST_DELAY','0.005')))
if role=='fail': code=7
emit('leave')
sys.exit(code)
'''


class SpawnSerializationTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name); self.tools=self.root/'native'; self.tools.mkdir()
        self.events=self.root/'events.jsonl'; self.lock=self.root/'shared.lock'
        self.wrappers={}
        for tool in p.e.BUILD_TOOL_NAMES:
            target=self.tools/tool; target.write_text(WORKER); target.chmod(0o755)
            data=p.launcher_bytes(tool).replace(b'/workspace/scratch/v17-build-process.lock',str(self.lock).encode()).replace(b'/opt/v17-toolchain/bin',str(self.tools).encode())
            wrapper=self.root/(tool+'-launcher'); wrapper.write_bytes(data); wrapper.chmod(0o755)
            self.wrappers[tool]=wrapper
        self.jobs=[]; self.addCleanup(self.cleanup_jobs)

    def cleanup_jobs(self):
        for job in self.jobs:
            if job.poll() is None:
                os.killpg(job.pid,signal.SIGKILL); job.wait(timeout=2)

    def start(self,tool,family,role='leaf',delay='0.005',wrapped=True,extra=None,cwd=None):
        env=os.environ.copy(); env.pop('V17_SERIAL_FAMILY',None)
        env.update(V17_TEST_EVENTS=str(self.events),V17_TEST_FAMILY=str(family),V17_TEST_DELAY=delay,V17_TEST_NESTED=str(self.wrappers['clang']))
        if extra: env.update(extra)
        job=subprocess.Popen([str(self.wrappers[tool] if wrapped else self.tools/tool),role],env=env,cwd=cwd or self.root,start_new_session=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        self.jobs.append(job); return job

    def records(self):
        return [json.loads(x) for x in self.events.read_text().splitlines()] if self.events.exists() else []

    def peak_families(self):
        active={}; peak=0
        for row in self.records():
            family=row['family']; active[family]=active.get(family,0)+(1 if row['phase']=='enter' else -1)
            peak=max(peak,sum(v>0 for v in active.values()))
        self.assertTrue(all(v==0 for v in active.values()))
        return peak

    def wait_enter(self):
        deadline=time.monotonic()+2
        while time.monotonic()<deadline:
            if self.records(): return
            time.sleep(0.005)
        self.fail('synthetic worker did not enter')

    def test_concurrent_short_lean_c_link_archive_jobs_are_preventively_serial(self):
        tools=['lean','clang','ld.lld','llvm-ar','leanc']*2
        jobs=[self.start(tool,i) for i,tool in enumerate(tools)]
        for job in jobs:
            _,err=job.communicate(timeout=5); self.assertEqual(job.returncode,0,err.decode())
        self.assertEqual(self.peak_families(),1)
        lean=[r for r in self.records() if r['tool']=='lean' and r['phase']=='enter']
        self.assertTrue(all(r['argv'][0]=='-j1' for r in lean))

    def test_cross_directory_jobs_share_one_lock_and_create_no_cwd_file(self):
        other=self.root/'other'; other.mkdir()
        jobs=[self.start('lean','one',delay='0.1'),self.start('clang','two',delay='0.1',cwd=other)]
        for job in jobs: job.communicate(timeout=5); self.assertEqual(job.returncode,0)
        self.assertEqual(self.peak_families(),1)
        self.assertFalse((self.root/'9').exists())
        self.assertFalse((other/'9').exists())

    def test_admission_waits_on_the_intended_lock_inode(self):
        with self.lock.open('w') as held:
            fcntl.flock(held,fcntl.LOCK_EX)
            job=self.start('clang','blocked')
            time.sleep(0.08)
            self.assertFalse(self.records())
            self.assertIsNone(job.poll())
            fcntl.flock(held,fcntl.LOCK_UN)
        job.communicate(timeout=3); self.assertEqual(job.returncode,0)

    def test_unwrapped_negative_control_detects_overlap(self):
        jobs=[self.start('clang',i,delay='0.15',wrapped=False) for i in range(6)]
        for job in jobs: job.communicate(timeout=5); self.assertEqual(job.returncode,0)
        self.assertGreater(self.peak_families(),1)

    def test_nested_native_child_inherits_lock_without_deadlock(self):
        jobs=[self.start('leanc','family','nested'),self.start('lean','other')]
        for job in jobs:
            _,err=job.communicate(timeout=5); self.assertEqual(job.returncode,0,err.decode())
        self.assertEqual(self.peak_families(),1)

    def test_stripped_family_descriptor_fails_closed(self):
        job=self.start('leanc','family','nested-stripped')
        job.communicate(timeout=3); self.assertEqual(job.returncode,125)
        self.assertFalse(any(r['tool']=='clang' for r in self.records()))

    def test_forged_family_token_does_not_spawn(self):
        job=self.start('clang','forged',extra={'V17_SERIAL_FAMILY':'1'})
        job.communicate(timeout=3); self.assertEqual(job.returncode,125)
        self.assertFalse(self.records())

    def test_native_failure_is_preserved(self):
        job=self.start('clang','fail','fail')
        job.communicate(timeout=3); self.assertEqual(job.returncode,7)

    def test_killed_waiter_never_spawns_and_does_not_release_owner(self):
        owner=self.start('lean','owner',delay='0.3'); self.wait_enter()
        waiter=self.start('clang','waiter')
        time.sleep(0.03); os.killpg(waiter.pid,signal.SIGKILL); waiter.communicate(timeout=2)
        successor=self.start('llvm-ar','successor')
        owner.communicate(timeout=3); successor.communicate(timeout=3)
        self.assertFalse(any(r['family']=='waiter' for r in self.records()))
        self.assertEqual(self.peak_families(),1)

    def test_owner_process_group_timeout_releases_lock(self):
        owner=self.start('lean','owner',delay='10'); self.wait_enter()
        os.killpg(owner.pid,signal.SIGKILL); owner.communicate(timeout=2)
        successor=self.start('clang','successor'); successor.communicate(timeout=3)
        self.assertEqual(successor.returncode,0)


if __name__=='__main__': unittest.main()
