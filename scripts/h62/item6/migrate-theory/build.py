#!/usr/bin/env python3
"""Serial, clean, uncached Lake module closure probe. Not the final run-lean gate.
Run under the repository writer lock. Private config never edits lean-toolchain.
"""
import argparse, hashlib, json, os, pathlib, resource, signal, subprocess, time
from census import ROOT, census
p=argparse.ArgumentParser(); p.add_argument('--toolchain',type=pathlib.Path,required=True); p.add_argument('--output',type=pathlib.Path,required=True); p.add_argument('--target',action='append',default=[]); p.add_argument('--fixture',type=pathlib.Path); a=p.parse_args()
a.output.mkdir(parents=True,exist_ok=False)
config=(ROOT/'lakefile.toml').read_text().replace('enableArtifactCache = true','enableArtifactCache = false').replace('["--tstack=131072"]','["--tstack=131072", "-j1", "-M10000"]')
config='buildDir = '+json.dumps(str(a.output/'build'))+'\n'+config
cfg=a.output/'lakefile.toml'; cfg.write_text(config)
env=dict(os.environ,PATH=str(a.toolchain/'bin')+':'+os.environ['PATH'],LEAN_NUM_THREADS='1',LAKE_ARTIFACT_CACHE='false')
versions={x:subprocess.check_output([str(a.toolchain/'bin'/x),'--version'],env=env,text=True).strip() for x in ['lean','lake']}
results={'versions':versions,'settings':{'lean_threads':1,'lean_args':['--tstack=131072','-j1','-M10000'],'reserve_bytes':4*1024**3,'aggregate_rss_limit_bytes':12*1024**3,'cache':'disabled, fresh buildDir','cpu_max':pathlib.Path('/sys/fs/cgroup/cpu.max').read_text().strip()},'modules':[]}
results['mode']='fixture-replay' if a.fixture else ('target-closure' if a.target else 'assigned-closure')
results['effective_LEAN_PATH']=env.get('LEAN_PATH','')
if a.fixture:
    results['settings']['cache']='direct Lean fixture; imports bundled libraries and any explicit LEAN_PATH artifacts; not a clean closure timing'
snapshot=census()
results['source_manifest_start']=snapshot['closure_source_sha256']
results['head']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
results['private_config_sha256']=hashlib.sha256(cfg.read_bytes()).hexdigest()
results['driver_sha256']=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
results['settings']['os_virtual_address_limit_bytes']=12*1024**3
results['settings']['rss_sampling_seconds']=.25
results['settings']['vm_memory_max']=pathlib.Path('/sys/fs/cgroup/memory.max').read_text().strip()
results['settings']['vm_swap_max']=pathlib.Path('/sys/fs/cgroup/memory.swap.max').read_text().strip()
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
if a.target and a.fixture: p.error('--target and --fixture are mutually exclusive')
if a.fixture:
    results['fixture_source_sha256']=hashlib.sha256(a.fixture.read_bytes()).hexdigest()
start=time.monotonic(); peak=0
order=census()['topological_closure']
if a.target:
    needed=set()
    def need(mod):
        if mod in needed: return
        if mod not in snapshot['edges']: raise ValueError('unknown project target: '+mod)
        needed.add(mod)
        for dep in snapshot['edges'][mod]:
            if dep in snapshot['edges']: need(dep)
    for mod in a.target: need(mod)
    order=[mod for mod in order if mod in needed]
    results['targets']=a.target
if a.fixture: order=[str(a.fixture)]
for mod in order:
    cmd=[str(a.toolchain/'bin/lake'),'-d',str(ROOT),'-f',str(cfg),'--no-cache','build','+'+mod+':olean']
    if a.fixture: cmd=[str(a.toolchain/'bin/lean'),'--tstack=131072','-j1','-M10000',str(a.fixture)]
    t=time.monotonic(); log=a.output/((a.fixture.stem if a.fixture else mod)+'.log'); reason=None; rss_peak=0
    with log.open('w') as f:
        proc=subprocess.Popen(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
        while proc.poll() is None:
            rss=0
            for stat in pathlib.Path('/proc').glob('[0-9]*/stat'):
                try:
                    fields=stat.read_text().rsplit(')',1)[1].split()
                    if int(fields[2])==proc.pid: rss+=int(fields[21])*os.sysconf('SC_PAGE_SIZE')
                except (OSError,ValueError,IndexError): pass
            rss_peak=max(rss_peak,rss); peak=max(peak,rss)
            avail=int(next(x.split()[1] for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024
            cgfree=int(pathlib.Path('/sys/fs/cgroup/memory.max').read_text())-int(pathlib.Path('/sys/fs/cgroup/memory.current').read_text())
            swap=int(pathlib.Path('/sys/fs/cgroup/memory.swap.current').read_text())
            if rss>12*1024**3 or min(avail,cgfree)<4*1024**3 or swap:
                reason='RESOURCE_STOP'; os.killpg(proc.pid,signal.SIGTERM); break
            time.sleep(.25)
        try: code=proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid,signal.SIGKILL); code=proc.wait(timeout=10)
    row={'module':mod,'command':cmd,'exit':code,'wall_s':time.monotonic()-t,'peak_group_rss_bytes_sampled':rss_peak,'log':str(log),'stop':reason}
    results['modules'].append(row)
    results.update(wall_s=time.monotonic()-start,peak_group_rss_bytes_sampled=peak,complete=False)
    (a.output/'result.json').write_text(json.dumps(results,indent=2)+'\n')
    print(f'{mod}: exit={code} wall={row["wall_s"]:.2f}s rss={rss_peak}',flush=True)
    if code or reason:
        results['source_manifest_end']=census()['closure_source_sha256']
        results['source_manifest_unchanged']=results['source_manifest_start']==results['source_manifest_end']
        (a.output/'result.json').write_text(json.dumps(results,indent=2)+'\n')
        raise SystemExit(code if code>0 else 1)
results['source_manifest_end']=census()['closure_source_sha256']
assert results['source_manifest_start']==results['source_manifest_end'], 'source tree changed during probe'
results['complete']=True
(a.output/'result.json').write_text(json.dumps(results,indent=2)+'\n')
print(('FIXTURE_PROBE_PASS' if a.fixture else 'CLOSURE_PROBE_PASS')+' (final run-lean.sh gate still required)',flush=True)
