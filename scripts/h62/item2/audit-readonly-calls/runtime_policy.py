"""Guard SDK-path substitution and VM guards silently replacing host guards."""
import ctypes
import hashlib
import os
from pathlib import Path, PurePosixPath
import re
import json
import pwd
import signal
import time
import uuid
import subprocess

GIB = 1024**3
CAP = 12*GIB
VM_RESERVE = 4*GIB
HOST_RESERVE = 12*GIB
WINDOW = 14400
DEFAULT_SDK = Path('/workspace/.setup/tools/lean-4.24.0-linux')
COMMIT = '797c613eb9b6d4ec95db23e3e00af9ac6657f24b'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sdk_configuration(mode, configured, root):
    require(mode in {'vm', 'host'}, 'unknown resource mode')
    require(mode != 'host' or configured is not None, 'host requires explicit --sdk')
    sdk = Path(configured if configured is not None else DEFAULT_SDK).resolve()
    require(all((sdk/'bin'/n).is_file() for n in ['lean', 'lake']), 'configured SDK missing; no fallback')
    toolchain = (root/'lean-toolchain').read_text().strip()
    require(toolchain == 'leanprover/lean4:v4.24.0', 'unapproved lean-toolchain')
    env = {k:v for k,v in os.environ.items() if not k.startswith(('LEAN_', 'ELAN_'))}
    version = subprocess.check_output([str(sdk/'bin/lean'), '--version'], env=env, text=True).strip()
    lake = subprocess.check_output([str(sdk/'bin/lake'), '--version'], env=env, text=True).strip()
    prefix = subprocess.check_output([str(sdk/'bin/lean'), '--print-prefix'], env=env, text=True).strip()
    require(re.search(r'version 4\.24\.0[, )]', version) and ('commit '+COMMIT) in version, 'SDK version/commit disagrees with toolchain')
    require(Path(prefix).resolve() == sdk, 'SDK prefix mismatch')
    require(COMMIT[:7] in lake, 'Lake commit mismatch')
    return sdk, dict(lean_version=version, lake_version=lake, sdk_root=str(sdk),
        lean_commit=COMMIT, lean_binary_sha256=hashlib.sha256((sdk/'bin/lean').read_bytes()).hexdigest(),
        lake_binary_sha256=hashlib.sha256((sdk/'bin/lake').read_bytes()).hexdigest(),
        toolchain_file_sha256=hashlib.sha256((root/'lean-toolchain').read_bytes()).hexdigest())


def effective_cgroup(proc=Path('/proc'), mountinfo=None):
    rows=(proc/'self/cgroup').read_text().splitlines()
    require(len(rows)==1 and rows[0].startswith('0::/'), 'unified cgroup required')
    path=PurePosixPath(rows[0][3:])
    require('..' not in path.parts, 'invalid cgroup path')
    mounts=(mountinfo if mountinfo is not None else (proc/'self/mountinfo').read_text()).splitlines()
    candidates=[]
    for row in mounts:
        left, sep, right=row.partition(' - ')
        if not sep or right.split()[0]!='cgroup2':continue
        fields=left.split()
        decode=lambda x: re.sub(r'\\([0-7]{3})', lambda m: chr(int(m[1],8)), x)
        source=PurePosixPath(decode(fields[3])); target=Path(decode(fields[4])).resolve()
        if path.is_relative_to(source):relative=path.relative_to(source)
        elif path==PurePosixPath('/'):relative=PurePosixPath('.')
        else:continue
        resolved=(target/str(relative)).resolve()
        require(resolved.is_relative_to(target), 'cgroup escapes mount')
        candidates.append((resolved,target))
    require(len(candidates)==1, 'effective cgroup mount ambiguous or missing')
    return candidates[0]


def memory_info(path):
    return {line.split(':')[0]:int(line.split()[1])*1024 for line in path.read_text().splitlines() if line.split(':')[0] in {'MemAvailable','SwapTotal'}}


class Guards:
    def __init__(self, mode, proc=Path('/proc'), vm_cgroup=Path('/sys/fs/cgroup')):
        require(mode in {'vm','host'}, 'unknown resource mode')
        self.mode,self.proc=mode,proc
        if mode=='host':self.cg,self.mount=effective_cgroup(proc)
        else:self.cg,self.mount=vm_cgroup,vm_cgroup
        self.initial=self.sample()

    def sample(self):
        info=memory_info(self.proc/'meminfo')
        if self.mode=='vm':
            limit=(self.cg/'memory.max').read_text().strip()
            require(limit!='max' and int(limit)>=CAP+VM_RESERVE, 'VM cap smaller than job+reserve')
            current=int((self.cg/'memory.current').read_text())
            swap=int((self.cg/'memory.swap.current').read_text())
            require(info.get('SwapTotal')==0 and swap==0, 'VM swap must be disabled')
            require(current<int(limit)-VM_RESERVE, 'VM 4GiB reserve guard')
            return dict(mode='vm',cgroup=str(self.cg),limit=int(limit),current=current,swap=swap,reserve=VM_RESERVE)
        require(effective_cgroup(self.proc)==(self.cg,self.mount), 'calling cgroup changed')
        bounds=[]; swaps=[]; node=self.cg
        while True:
            # The real cgroup-v2 mount root may have no limit files. Bounds
            # must still be established in the actual scoped ancestors below.
            if node==self.mount and not (node/'memory.max').exists():break
            maximum=(node/'memory.max').read_text().strip()
            swapmax=(node/'memory.swap.max').read_text().strip()
            swapcurrent=int((node/'memory.swap.current').read_text())
            if maximum!='max':bounds.append((int(maximum),int((node/'memory.current').read_text()),str(node)))
            if swapmax!='max':swaps.append((int(swapmax),swapcurrent))
            if node==self.mount:break
            node=node.parent
        require(bounds and min(x[0] for x in bounds)<=CAP, 'host lacks <=12GiB effective memory cap')
        require(swaps and min(x[0] for x in swaps)==0, 'host lacks effective zero-swap cap')
        require(all(current==0 for maximum,current in swaps if maximum==0), 'host scoped swap in use')
        require(all(current<limit for limit,current,_ in bounds), 'host cgroup memory cap reached')
        require(info.get('MemAvailable',0)>=HOST_RESERVE, 'host 12GiB available-memory reserve guard')
        limit=min(x[0] for x in bounds)
        return dict(mode='host',cgroup=str(self.cg),limit=limit,bounds=bounds,reserve=HOST_RESERVE,available=info['MemAvailable'],swap=0)


def subreaper():
    # Keep escaped orphan descendants attributable to this monitor for cleanup.
    libc=ctypes.CDLL(None,use_errno=True)
    require(libc.prctl(36,1,0,0,0)==0, 'cannot enable child subreaper')


class Descendants:
    def __init__(self, leader, proc=Path('/proc')):
        self.leader=leader;self.proc=proc;self.known={};self.started={}
    def sample(self):
        rows={}
        # Establish ownership from stat BEFORE mandatory detailed reads. A
        # first-seen nondumpable orphan must not disappear from the census.
        for entry in self.proc.iterdir():
            if not entry.name.isdecimal():continue
            try:
                fields=(entry/'stat').read_text().rsplit(')',1)[1].split()
                pid=int(entry.name)
                rows[pid]=dict(state=fields[0],pid=pid,ppid=int(fields[1]),pgid=int(fields[2]),start=fields[19])
            except (OSError,ProcessLookupError):
                if entry.exists():
                    raise ValueError('owned basic process observation unavailable' if int(entry.name) in self.known else 'process ancestry observation unavailable')
        owned={p for p,r in rows.items() if p==self.leader or r['pgid']==self.leader or (p in self.known and self.known[p]==r['start']) or r['ppid']==os.getpid()}
        while True:
            expanded=owned|{p for p,r in rows.items() if r['ppid'] in owned}
            if expanded==owned:break
            owned=expanded
        for pid in owned:self.known[pid]=rows[pid]['start']
        result=[]
        for pid in owned:
            row=rows[pid];entry=self.proc/str(pid)
            if row['state']=='Z':row.update(rss=0,argv=[],exe='',exe_path='')
            else:
                try:
                    status=(entry/'status').read_text().splitlines()
                    row['rss']=sum(int(x.split()[1])*1024 for x in status if x.startswith('VmRSS:'))
                    row['argv']=(entry/'cmdline').read_bytes().decode(errors='replace').rstrip('\0').split('\0')
                    row['exe_path']=str((entry/'exe').resolve(strict=True))
                    row['exe']=Path(row['exe_path']).name.removesuffix(' (deleted)')
                except (OSError,ProcessLookupError):
                    if entry.exists():raise ValueError('owned detailed process observation unavailable')
                    continue
            result.append(row)
        return result


def serial_reason(members, now, started, proof_timeout, expected_lean=None):
    lean=[r for r in members if r['exe']=='lean']
    if len(lean)>1:return 'multiple Lean processes; serial gate required'
    for r in lean:
        if expected_lean is not None and Path(r['exe_path']).resolve()!=Path(expected_lean).resolve():return 'observed Lean SDK mismatch'
        argv=r['argv']
        if '--version' not in argv:
            if '-j1' not in argv or any((x.startswith('-j') and x!='-j1') or x.startswith('--threads') for x in argv):return 'Lean argv requires explicit -j1 only'
        key=(r['pid'],r['start']);started.setdefault(key,now)
        if now-started[key]>proof_timeout:return 'per-module proof deadline'
    return None


class AggregateWindow:
    """Task-owned state cannot reset through a new evidence path or HOME/XDG."""
    def __init__(self, directory=None):
        home=Path(pwd.getpwuid(os.getuid()).pw_dir)
        self.directory=Path(directory) if directory is not None else home/'.local/state/solidity-lean-audit-readonly-calls'
        self.directory.mkdir(parents=True,exist_ok=True,mode=0o700)
        self.path=self.directory/'aggregate-window.json'
        self.data=json.loads(self.path.read_text()) if self.path.exists() else {'spent':0.0,'inflight':None}
        require(self.data.get('inflight') is None,'incomplete prior monitor: aggregate window requires explicit recovery')
        require(isinstance(self.data.get('spent'),(int,float)) and 0<=self.data['spent']<WINDOW,'aggregate 14400s window exhausted or invalid')
        self.spent=self.data['spent'];self.token=None
    def write(self,data):
        temp=self.directory/('window-'+uuid.uuid4().hex+'.tmp')
        with temp.open('x') as stream:
            json.dump(data,stream);stream.flush();os.fsync(stream.fileno())
        os.replace(temp,self.path)
        fd=os.open(self.directory,os.O_RDONLY)
        try:os.fsync(fd)
        finally:os.close(fd)
    def reserve(self,requested):
        require(0<requested<=WINDOW,'invalid group deadline')
        deadline=min(requested,WINDOW-self.spent)
        self.token=uuid.uuid4().hex
        self.write({'spent':self.spent+deadline,'inflight':{'token':self.token,'monitor_pid':os.getpid(),'reserved_seconds':deadline}})
        return deadline
    def finish(self,elapsed):
        require(elapsed>=0,'invalid elapsed time')
        data=json.loads(self.path.read_text())
        require(data.get('inflight',{}).get('token')==self.token,'aggregate reservation changed')
        self.write({'spent':self.spent+elapsed,'inflight':None})


def drain_owned(tracker, group, sleeper=time.sleep, note=lambda message:None):
    """Never return (or unwind) without a positive observation of no live child."""
    failures=[];reported=False
    while True:
        try:
            rows=tracker.sample()
            if not any(r['state']!='Z' for r in rows):return failures
        except BaseException as error:

            if len(failures)<16:failures.append(type(error).__name__+': '+str(error))
        try:
            if not reported:
                note('owned cleanup pending; writer lock retained');reported=True
            try:os.killpg(group,signal.SIGKILL)
            except ProcessLookupError:pass
            for pid,start in list(tracker.known.items()):
                try:
                    stat=(Path('/proc')/str(pid)/'stat').read_text().rsplit(')',1)[1].split()
                    if stat[19]==start and stat[0]!='Z':os.kill(pid,signal.SIGKILL)
                except (OSError,ProcessLookupError):pass
            sleeper(0.1)
        except BaseException as error:

            if len(failures)<16:failures.append(type(error).__name__+': '+str(error))
