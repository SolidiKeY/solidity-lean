#!/usr/bin/env python3
"""Serial measured sample, dependency cache only (never build cold imports).
Run from repository root with Lean/Lake/elan on PATH:
python3 docs/audits/direction-tools/timing/measure.py --repo /absolute/clean/checkout --work /absolute/external/dir [--profiles] [--only PATH] --cloud-vm
Use a fresh --work directory to retime a path; saved observations are reused.
Cloud execution under H232 requires explicit --cloud-vm. Host execution is unsupported;
use the repository host scope/12 GiB reserve policy there. No relaxed defaults.
External logs contain full profiler output; small result JSON is in --work.
The caller MUST hold the shared writer lock. No Lean sources are written.
"""
import argparse,json,os,pathlib,re,signal,shutil,subprocess,tempfile,time
CLOUD_VM_OPT_IN=False
HERE=pathlib.Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def atomic_write_json(path,data):
    path=pathlib.Path(path)
    fd,name=tempfile.mkstemp(prefix='.'+path.name+'.',suffix='.tmp',dir=path.parent)
    try:
        with os.fdopen(fd,'w',encoding='utf-8') as handle:
            json.dump(data,handle,indent=2); handle.write('\n'); handle.flush(); os.fsync(handle.fileno())
        os.replace(name,path)
        directory=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY)
        try: os.fsync(directory)
        finally: os.close(directory)
    finally:
        try: os.unlink(name)
        except FileNotFoundError: pass

def capture_environment(repo):
    meminfo=pathlib.Path('/proc/meminfo').read_text()
    return {'metadata_scope':'latest runner invocation only; resumed rows retain original per-observation metadata or null','cloud_vm_opt_in':CLOUD_VM_OPT_IN,'isolation':'H232 cloud VM; no systemd scope' if CLOUD_VM_OPT_IN else 'unasserted','swap_total_kib':int(re.search(r'^SwapTotal:\s+(\d+)',meminfo,re.M)[1]),'lean_num_threads':1,'rss_stop_kib':12*1024**2,'available_memory_stop_kib':3*1024**2,'measurement_checkout':str(repo),'tracked_source_clean':not subprocess.check_output(['git','-C',str(repo),'status','--porcelain','--untracked-files=no'],text=True).strip()}

def active_compilers(exclude_group=None):
    """Fail closed if /proc cannot establish VM-wide compiler isolation.

    Zombies do not execute. Never signal processes discovered by this scan;
    the command helper may terminate only the new session it created itself.
    """
    found=[]
    for entry in pathlib.Path('/proc').iterdir():
        if not entry.name.isdigit(): continue
        try:
            status=(entry/'status').read_text()
            name=re.search(r'^Name:\s+(\S+)',status,re.M)[1]
            state=re.search(r'^State:\s+(\S+)',status,re.M)[1]
            if name not in ('lean','lake') or state=='Z': continue
            pid=int(entry.name)
            if exclude_group is None or os.getpgid(pid)!=exclude_group: found.append(pid)
        except FileNotFoundError: continue
        except ProcessLookupError: continue
    return found

def terminate_owned_session(proc):
    """Only for the fresh session created by command(), never discovered PIDs.

    Kill the group even if its leader exits promptly: descendants may survive
    TERM. A group with no remaining members simply yields ProcessLookupError.
    """
    try: os.killpg(proc.pid,signal.SIGTERM)
    except ProcessLookupError: pass
    try: proc.wait(timeout=5)
    except subprocess.TimeoutExpired: pass
    try: os.killpg(proc.pid,signal.SIGKILL)
    except ProcessLookupError: pass
    proc.wait()

def command(args,cwd,log,timeout=600):
    if not CLOUD_VM_OPT_IN: raise RuntimeError('cloud-only runner requires explicit --cloud-vm; host resource policy is not implemented')
    if int(re.search(r'^SwapTotal:\s+(\d+)',pathlib.Path('/proc/meminfo').read_text(),re.M)[1])!=0: raise RuntimeError('cloud runner requires swap disabled')
    foreign=active_compilers()
    if foreign: raise RuntimeError('another active Lean/Lake process exists; refusing overlap: '+repr(foreign))
    start=time.monotonic(); peak=0; reason=None; peak_workers=0
    with log.open('w') as f:
        proc=subprocess.Popen(args,cwd=cwd,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
        try:
            while proc.poll() is None:
                # Conservative summed RSS of this command process group, including
                # shared pages; stop at 12 GiB or below 3 GiB available OS memory.
                rss=0; workers=0
                for entry in pathlib.Path('/proc').iterdir():
                    if not entry.name.isdigit(): continue
                    try:
                        if os.getpgid(int(entry.name))!=proc.pid: continue
                        status=(entry/'status').read_text()
                        if re.search(r'^Name:\s+lean$',status,re.M): workers+=1
                        match=re.search(r'^VmRSS:\s+(\d+)',status,re.M)
                        if match: rss+=int(match.group(1))
                    except (OSError,ProcessLookupError): pass
                peak=max(peak,rss); peak_workers=max(peak_workers,workers)
                available=int(re.search(r'MemAvailable:\s+(\d+)',pathlib.Path('/proc/meminfo').read_text())[1])
                if time.monotonic()-start>timeout: reason='timeout'
                elif rss>12*1024**2 or available<3*1024**2: reason='memory_guard'
                elif workers>1 or active_compilers(exclude_group=proc.pid): reason='concurrent_lean_guard'
                elif shutil.disk_usage(cwd).free<2*1024**3: reason='disk_guard'
                if reason:
                    terminate_owned_session(proc)
                    break
                try: proc.wait(timeout=0.1)
                except subprocess.TimeoutExpired: pass
        except BaseException:
            # This session was created by this Popen invocation. Never terminate
            # PIDs returned by the VM-wide scan: those may belong to other work.
            terminate_owned_session(proc)
            raise
        code=proc.wait() if reason is None else (124 if reason=='timeout' else 125)
    return {'command':args,'cwd':str(cwd),'exit_code':code,'wall_seconds':time.monotonic()-start,'peak_sampled_group_rss_kib':peak,'peak_sampled_lean_workers':peak_workers,'stop_reason':reason,'log':str(log)}
def main():
    global ROOT, CLOUD_VM_OPT_IN
    ap=argparse.ArgumentParser(); ap.add_argument('--cloud-vm',action='store_true',help='explicit opt-in to H232 cloud VM isolation; unsupported on hosts'); ap.add_argument('--profiles',action='store_true'); ap.add_argument('--only',action='append',default=[],help='measure only these exact planned paths; preserve all saved rows'); ap.add_argument('--repo',type=pathlib.Path,required=True); ap.add_argument('--work',type=pathlib.Path,required=True); args=ap.parse_args(); ROOT=args.repo.resolve()
    if not args.cloud_vm: ap.error('execution requires explicit --cloud-vm under H232; host execution unsupported')
    CLOUD_VM_OPT_IN=True
    args.work.mkdir(parents=True,exist_ok=True)
    environment=capture_environment(ROOT)
    if environment['swap_total_kib']!=0: ap.error('cloud timing runner requires swap disabled before execution')
    assert subprocess.check_output(['git','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip()=='d6fd95f0886775d7c286813fa9b993a40ba7a777'
    assert not subprocess.check_output(['git','-C',str(ROOT),'status','--porcelain','--untracked-files=no'],text=True).strip(), 'dirty measured source'
    data=json.loads((HERE/'inventory.json').read_text())
    assert len({r['path'] for r in data['sample_plan']})==len(data['sample_plan']), 'duplicate plan paths'
    if set(args.only)-{r['path'] for r in data['sample_plan']}: ap.error('--only path is not in the committed plan')
    saved=args.work/'sample-results.json'
    saved_rows=json.loads(saved.read_text())['samples'] if saved.exists() else []
    previous={r['path']:r for r in saved_rows}
    assert len(previous)==len(saved_rows), 'duplicate saved observation paths'
    results=dict(previous)
    versions={}
    for name in ('lean','lake'):
        versions[name]=subprocess.check_output([name,'--version'],text=True).strip()
    if saved.exists():
        prior=json.loads(saved.read_text())
        assert prior['base']==data['base'] and prior['versions']==versions, 'resume base/toolchain mismatch'
        for row in prior['samples']:
            expected=ROOT/'Bridge' if row['path'].startswith('Bridge/') else ROOT
            assert row['cache']['cwd']==str(expected), 'resume measurement checkout mismatch'
            if 'plain' in row: assert row['plain']['cwd']==str(expected), 'resume plain checkout mismatch'
    key=command(['lake','env','lean','-j1','Solidity/KeySort.lean'],ROOT,args.work/'KeySort.log')
    if key['exit_code']: raise SystemExit('KeySort failed: '+key['log'])
    for i,row in enumerate(data['sample_plan']):
        if args.only and row['path'] not in args.only: continue
        p=row['path']; bridge=p.startswith('Bridge/'); cwd=ROOT/'Bridge' if bridge else ROOT
        file=p.removeprefix('Bridge/') if bridge else p
        module=file.removesuffix('.lean').replace('/','.')
        item={**previous.get(p,{}),**row,'module':module,'toolchain':versions['lean'],'observation_environment':previous[p].get('observation_environment') if p in previous else environment}
        if 'cache' not in item: item['cache']=command(['lake','--no-build','build','+'+module+':deps'],cwd,args.work/f'{i:02}-cache.log',180)
        if item['cache']['exit_code']:
            item['status']='dependency-cache-unavailable'
        else:
            if 'plain' not in item: item['restore']=command(['python3',str(ROOT/'scripts/ci/restore-lake-artifacts.py'),str(cwd)],ROOT,args.work/f'{i:02}-restore.log')
            if 'plain' not in item: item['plain']=command(['lake','env','lean','-j1','--tstack=131072',file],cwd,args.work/f'{i:02}-plain.log')
            item['status']='pass' if item['plain']['exit_code']==0 else 'fail'
            if item['status']=='pass':
                item['seconds_per_kloc']=1000*item['plain']['wall_seconds']/row['lines']
                if args.profiles and (not item.get('profile',{}).get('exit_code')==0 or not (args.work/f'{i:02}-trace.json').exists()): item['profile']=command(['lake','env','lean','-j1','--tstack=131072','-Dprofiler=true','-Dprofiler.threshold=100000000','-Dtrace.profiler=true','-Dtrace.profiler.threshold=100','-Dtrace.profiler.output='+str(args.work/f'{i:02}-trace.json'),'-Dtrace.profiler.output.pp=true',file],cwd,args.work/f'{i:02}-profiler.log')
        results[p]=item
        planned=[r['path'] for r in data['sample_plan']]
        checkpoint_rows=[results[path] for path in planned if path in results]+[value for path,value in results.items() if path not in set(planned)]
        atomic_write_json(args.work/'sample-results.json',{'base':data['base'],'versions':versions,'environment':environment,'KeySort':key,'conditions':'one worker, -j1, LEAN_NUM_THREADS=1, cache-only dependencies, no systemd scope on the cloud VM (H232); plain run before profiled run; one observation, OS page cache uncontrolled','samples':checkpoint_rows})
        print(i,p,item['status'],flush=True)
if __name__=='__main__': main()
