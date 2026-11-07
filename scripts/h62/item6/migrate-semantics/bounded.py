#!/usr/bin/env python3
"""Serial guards: conservative AS bound or verified cgroup memory cap on Linux."""
import os, resource, signal, subprocess, time, json, re
from pathlib import Path

MODULE_CAP_BYTES = 8 * 1024**3
RESERVE_BYTES = 4 * 1024**3
MODULE_TIMEOUT_SECONDS = 300

def controller_mount(path):
    for line in Path('/proc/self/mountinfo').read_text().splitlines():
        fields=line.split(); split=fields.index('-')
        if fields[4]==str(path) and fields[split+1]=='cgroup2':
            return {'device':fields[2],'root':fields[3],'mount':fields[4]}
    raise RuntimeError('H78_CONTROLLER_MOUNT_UNVERIFIED')

def cap_kind():
    kind=os.environ.get('H78_CAP_KIND','address-space')
    if kind not in ['address-space','cgroup']:
        raise RuntimeError('H78_UNKNOWN_CAP_KIND')
    if kind=='cgroup':
        cg=Path('/sys/fs/cgroup')
        if (cg/'memory.max').read_text().strip()!=str(MODULE_CAP_BYTES) or (cg/'memory.swap.max').read_text().strip()!='0':
            raise RuntimeError('H78_CGROUP_CAP_UNVERIFIED')
        parent=os.environ.get('H78_VM_CGROUP')
        if not parent or not Path(parent,'memory.max').is_file():
            raise RuntimeError('H78_VM_CONTROLLER_REQUIRED')
        job=controller_mount('/sys/fs/cgroup'); vm=controller_mount(parent)
        marker=os.environ.get('H78_CONTROLLER_ID_FILE')
        if not marker: raise RuntimeError('H78_CONTAINER_ID_REQUIRED')
        cid=json.loads(Path(marker).read_text()).get('container_id','')
        if not re.fullmatch('[0-9a-f]{64}',cid): raise RuntimeError('H78_CONTAINER_ID_INVALID')
        # Mount-root strings are namespace-relative and can contain /.. .
        # Compare the actual kernfs node instead of interpreting those strings.
        try: under_vm=(Path(parent)/'docker'/cid).stat()
        except FileNotFoundError: raise RuntimeError('H78_VM_CONTROLLER_NOT_ANCESTOR') from None
        actual=Path('/sys/fs/cgroup').stat()
        if job['device']!=vm['device'] or (under_vm.st_dev,under_vm.st_ino)!=(actual.st_dev,actual.st_ino):
            raise RuntimeError('H78_VM_CONTROLLER_NOT_ANCESTOR')
        maximum=Path(parent,'memory.max').read_text().strip()
        if maximum!='max' and int(maximum)<MODULE_CAP_BYTES+RESERVE_BYTES:
            raise RuntimeError('H78_VM_RESERVE_UNAVAILABLE')
    return kind

def settings():
    result={'reserve_bytes': RESERVE_BYTES,'module_timeout_seconds': MODULE_TIMEOUT_SECONDS,
            'threads': 1,'rss_measurement': 'Linux wait4 ru_maxrss, KiB, per child process'}
    if cap_kind()=='cgroup':
        result.update(memory_max_bytes=MODULE_CAP_BYTES,memory_swap_max_bytes=0,
                      cap_mechanism='verified cgroup-v2 job memory cap')
    else:
        result['address_space_bytes']=MODULE_CAP_BYTES
    return result

def passed(result):
    return result['exit']==0 and result['stop'] is None

def available():
    host=int(next(s.split()[1] for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:')))*1024
    kind=cap_kind(); cg=Path(os.environ['H78_VM_CGROUP']) if kind=='cgroup' else Path('/sys/fs/cgroup'); cap=(cg/'memory.max').read_text().strip(); used=int((cg/'memory.current').read_text())
    return min(host,int(cap)-used) if cap!='max' else host

def limits():
    if cap_kind()=='address-space':
        resource.setrlimit(resource.RLIMIT_AS,(MODULE_CAP_BYTES,MODULE_CAP_BYTES))
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))

def run(command, *, log, cwd=None, env=None, timeout_seconds=MODULE_TIMEOUT_SECONDS):
    if available()<RESERVE_BYTES:
        return {'exit':None,'stop':'RESOURCE_BLOCK','wall_seconds':0.0,'peak_rss_kib':None}
    started=time.monotonic(); reason=None; usage=None
    with Path(log).open('w') as stream:
        child=subprocess.Popen(command,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT,
                               preexec_fn=limits,start_new_session=True)
        def reap(block):
            nonlocal usage
            if not block:
                event=os.waitid(os.P_PID,child.pid,os.WEXITED|os.WNOHANG|os.WNOWAIT)
                if event is None: return False
                # Keep the exited leader unreaped while killing its owned group,
                # so its PID cannot be reused before descendant cleanup.
                kill_owned_group()
            pid,status,measured=os.wait4(child.pid,0)
            usage=measured; child.returncode=os.waitstatus_to_exitcode(status)
            return True
        def kill_owned_group():
            try: os.killpg(child.pid,signal.SIGKILL)
            except ProcessLookupError: pass
        try:
            while not reap(False):
                if available()<RESERVE_BYTES:
                    reason='RESOURCE_BLOCK'; kill_owned_group(); reap(True); break
                if time.monotonic()-started>timeout_seconds:
                    reason='MODULE_300S_STOP' if timeout_seconds==MODULE_TIMEOUT_SECONDS else 'TEST_TIMEOUT'
                    kill_owned_group(); reap(True); break
                time.sleep(.25)
        finally:
            if child.returncode is None:
                kill_owned_group(); reap(True)
    return {'exit':child.returncode,'stop':reason,'wall_seconds':time.monotonic()-started,
            'peak_rss_kib':usage.ru_maxrss}
