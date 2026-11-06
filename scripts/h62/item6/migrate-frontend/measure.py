#!/usr/bin/env python3
"""Serial clean Lake module measurement. Bulk logs/build products stay off Git.

The census topological closure prevents Lake from finding unbuilt local imports
when each module starts. No artifacts are fetched; a new build directory is
required. This is a lane build, not run-lean.sh or the full root acceptance gate.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

GIB = 1024**3
CAP = 12*GIB
RESERVE = 4*GIB

def usage():
    # Poll only our process group; never signal another session's jobs.
    rows = []
    for path in Path('/proc').glob('[0-9]*/stat'):
        try:
            text = path.read_text()
            fields = text[text.rfind(')')+2:].split()
            rows.append((int(path.parent.name), int(fields[2]), int(fields[21])*os.sysconf('SC_PAGE_SIZE'), int(fields[20]), int(fields[17])))
        except (OSError, ValueError, IndexError): pass
    return rows

def available():
    vals = dict(line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())
    host = int(vals['MemAvailable'].split()[0])*1024
    cap = Path('/sys/fs/cgroup/memory.max').read_text().strip()
    used = int(Path('/sys/fs/cgroup/memory.current').read_text())
    return min(host, int(cap)-used) if cap != 'max' else host

def child_limits():
    # The VM already has a hard cgroup memory cap. Stack reservations are
    # virtual, not RSS; RLIMIT_AS can break bounded --tstack=131072 checks.
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

def run(cmd, root, env, logfile):
    if available() < RESERVE: raise RuntimeError('RESOURCE_HEADROOM_STOP')
    peak = 0
    peak_virtual = 0
    peak_threads = 0
    start = time.monotonic()
    stop = None
    def interrupted(signum, frame):
        raise InterruptedError('Interrupted by signal '+str(signum))
    previous = {sig: signal.signal(sig, interrupted) for sig in (signal.SIGINT, signal.SIGTERM)}
    p = None
    try:
        with logfile.open('w') as log:
            p = subprocess.Popen(cmd, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT,
                                 start_new_session=True, preexec_fn=child_limits)
            while p.poll() is None:
                rows = [row for row in usage() if row[1] == p.pid]
                rss = sum(row[2] for row in rows)
                peak_virtual = max(peak_virtual, sum(row[3] for row in rows))
                peak_threads = max(peak_threads, sum(row[4] for row in rows))
                peak = max(peak, rss)
                if rss > CAP or available() < RESERVE:
                    stop = 'RESOURCE_CAP_STOP' if rss > CAP else 'RESOURCE_HEADROOM_STOP'
                    break
                time.sleep(0.1)
    except BaseException as exc:
        stop = type(exc).__name__+': '+str(exc)
    finally:
        # Repeated interrupts must not interrupt owned-child teardown.
        for sig in previous: signal.signal(sig, signal.SIG_IGN)
        try:
            if p is not None:
                try: os.killpg(p.pid, signal.SIGTERM)
                except ProcessLookupError: pass
                try: p.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    try: os.killpg(p.pid,signal.SIGKILL)
                    except ProcessLookupError: pass
                    p.wait()
                try: os.killpg(p.pid, signal.SIGKILL)
                except ProcessLookupError: pass
        finally:
            for sig, handler in previous.items(): signal.signal(sig, handler)
    return {'command':cmd,'exit':p.returncode if p is not None else None,'wall_seconds':round(time.monotonic()-start,6),
            'peak_group_rss_bytes_sampled':peak,'peak_group_virtual_bytes_sampled':peak_virtual,
            'peak_group_threads_sampled':peak_threads,'stop':stop,'log':str(logfile)}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,default=Path.cwd())
    ap.add_argument('--toolchain',type=Path,required=True)
    ap.add_argument('--census',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--only',help='single module and its dependencies from the closure')
    args=ap.parse_args()
    root=args.root.resolve()
    out=args.out.resolve()
    if out.exists(): raise SystemExit('Refusing to reuse measurement directory')
    lock=Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock').open('a')
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    subprocess.run(['git','status','--short'],cwd=root,check=True)
    census=json.loads(args.census.read_text())
    for row in census['closure_sources'] + census['scope_files']:
        if hashlib.sha256((root/row['path']).read_bytes()).hexdigest()!=row['sha256']:
            raise SystemExit('Frozen source mismatch: '+row['path'])
    targets=census['topological_closure']
    if args.only:
        required=set()
        def visit(m):
            if m in required or m not in census['closure_imports']: return
            required.add(m)
            for d in census['closure_imports'][m]: visit(d)
        if args.only not in targets: raise SystemExit('Target absent from census')
        visit(args.only)
        targets=[m for m in targets if m in required]
    swap = next(line for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('SwapTotal:'))
    if int(swap.split()[1]) != 0: raise SystemExit('No-swap prerequisite failed')
    cpu=min(os.sched_getaffinity(0))
    os.sched_setaffinity(0,{cpu})
    out.mkdir(parents=True)
    # Absolute external buildDir separates versions and prohibits old per-master caches.
    config=(root/'lakefile.toml').read_text().replace('enableArtifactCache = true','enableArtifactCache = false')
    config=config.replace('version = "0.1.0"','version = "0.1.0"\nbuildDir = '+json.dumps(str(out/'build')))
    config=config.replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1", "-DElab.async=false"]')
    private=out/'lakefile.toml'
    private.write_text(config)
    env=dict(os.environ,PATH=str(args.toolchain.resolve()/'bin')+':'+os.environ['PATH'],
             LEAN_NUM_THREADS='1',LAKE_ARTIFACT_CACHE='false')
    lake=str(args.toolchain.resolve()/'bin/lake')
    lean=str(args.toolchain.resolve()/'bin/lean')
    versions={name:subprocess.check_output([exe,'--version'],text=True,env=env).strip() for name,exe in [('lean',lean),('lake',lake)]}
    meta={'versions':versions,'settings':{'lean_num_threads_env':1,'lean_args':['--tstack=131072','-j1','-DElab.async=false'],
           'rss_monitor_cap_bytes':CAP,'virtual_address_cap':None,'vm_hard_memory_cap':Path('/sys/fs/cgroup/memory.max').read_text().strip(),'reserve_bytes':RESERVE,'swap_bytes':0,'poll_seconds':0.1,
           'artifact_cache':False,'clean_build':True,'cpu_affinity':[cpu],'os_page_cache':'uncontrolled; no cache-dropping permission'},
          'root':str(root),'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
          'census_sha256':hashlib.sha256(args.census.read_bytes()).hexdigest(),
          'tracked_lakefile_sha256':hashlib.sha256((root/'lakefile.toml').read_bytes()).hexdigest(),
          'private_config_sha256':hashlib.sha256(private.read_bytes()).hexdigest(),
          'observed_swap_total':swap,'targets':targets,'results':[]}
    start=time.monotonic()
    for n,m in enumerate(targets):
        command=[lake,'--dir',str(root),'--file',str(private),'--no-cache','build','+'+m]
        try:
            row=run([lake,'--dir',str(root),'--file',str(private),'--no-cache','build','+'+m],root,env,out/f'{n:04d}-{m}.log')
        except Exception as exc:
            row={'command':command,'exit':None,'wall_seconds':0,'peak_group_rss_bytes_sampled':0,
                 'stop':type(exc).__name__+': '+str(exc),'log':None}
        row['module']=m
        meta['results'].append(row)
        meta['wall_seconds']=round(time.monotonic()-start,6)
        meta['peak_group_rss_bytes_sampled']=max(x['peak_group_rss_bytes_sampled'] for x in meta['results'])
        meta['status']='running' if row['exit']==0 and row['stop'] is None else 'failed'
        (out/'measurement.json').write_text(json.dumps(meta,indent=2)+'\n')
        print(f"{n+1}/{len(targets)} {m} exit={row['exit']} wall={row['wall_seconds']} rss={row['peak_group_rss_bytes_sampled']}",flush=True)
        if row['exit']!=0 or row['stop'] is not None: raise SystemExit(1)
    meta['status']='pass'
    (out/'measurement.json').write_text(json.dumps(meta,indent=2)+'\n')

if __name__=='__main__': main()
