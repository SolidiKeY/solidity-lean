#!/usr/bin/env python3
import json,os,signal,subprocess,sys,time,threading,resource
from pathlib import Path
record=Path(sys.argv[1]); command=sys.argv[2:]
tag='tv-yul-prototype-1108'
reserve=4*1024**3
use_vm_cap=os.environ.get('TVYUL_USE_VM_CAP')=='1'
def under_reserve(sample):
    return sample['os_available']<reserve or (not use_vm_cap and sample['effective_free']<reserve)

def resources():
    cg=Path('/sys/fs/cgroup')
    limit=int((cg/'memory.max').read_text())
    if use_vm_cap: assert limit<=16*1024**3, 'VM-cap opt-in requires hard cap at most16GiB'
    current=int((cg/'memory.current').read_text())
    stats=dict(row.split() for row in (cg/'memory.stat').read_text().splitlines())
    inactive=int(stats['inactive_file'])
    mem={row.split(':')[0]:int(row.split()[1])*1024 for row in Path('/proc/meminfo').read_text().splitlines() if len(row.split())>=3}
    assert mem['SwapTotal']==0,'swap must remain unavailable'
    return dict(limit=limit,current=current,working=current-inactive,effective_free=limit-current+inactive,os_available=mem['MemAvailable'])

samples=[resources()]; start=time.monotonic(); stopped=False
if under_reserve(samples[0]):
    code=125; stopped=True
else:
    child=subprocess.Popen(command,env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_LSP_MAX_OPEN_FILES='3',TVYUL_RESOURCE_TAG=tag),start_new_session=True)
    finished=threading.Event()
    def monitor():
        global stopped
        while not finished.wait(.25):
            sample=resources(); samples.append(sample)
            if under_reserve(sample):
                stopped=True
                marker=('TVYUL_RESOURCE_TAG='+tag).encode()
                for proc in Path('/proc').iterdir():
                    if not proc.name.isdigit() or int(proc.name)==os.getpid(): continue
                    try:
                        if marker in (proc/'environ').read_bytes().split(b'\0'):
                            os.kill(int(proc.name),signal.SIGTERM)
                    except (OSError,ProcessLookupError): pass
                break
    watcher=threading.Thread(target=monitor,daemon=True);watcher.start()
    code=child.wait(); elapsed=time.monotonic()-start
    finished.set();watcher.join()
    if stopped: code=125
result=dict(command=command,exit=code,seconds=elapsed if not stopped else time.monotonic()-start,child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,resource_stop=stopped,vm_cap_opt_in=use_vm_cap,policy=('H232 explicit VM-cap opt-in: unchanged16GiB hard cgroup bound; no swap; 4GiB OS headroom; no extra inactive-file working-set cap; no virtual-address cap' if use_vm_cap else 'H232 VM cgroup bound; no swap; 4GiB OS and effective working-set headroom; no virtual-address cap'),cgroup_limit=samples[0]['limit'],peak_cgroup_current=max(s['current'] for s in samples),peak_cgroup_working=max(s['working'] for s in samples),minimum_effective_free=min(s['effective_free'] for s in samples),minimum_os_available=min(s['os_available'] for s in samples))
record.parent.mkdir(parents=True,exist_ok=True);record.write_text(json.dumps(result,indent=2)+'\n')
print('RESOURCE_CHECK',json.dumps(result),flush=True)
sys.exit(code if code>=0 else 128-code)
