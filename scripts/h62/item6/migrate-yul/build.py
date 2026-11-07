#!/usr/bin/env python3
"""Serial clean Lake module build with private per-toolchain artifacts and RSS guard.
No source/config/toolchain writes in the checkout; no shared/master cache.
"""
import sys
sys.dont_write_bytecode = True
from resources import snapshot
import atexit, argparse, fcntl, hashlib, json, os, pathlib, re, signal, subprocess, time
p=argparse.ArgumentParser()
p.add_argument('--root',type=pathlib.Path,required=True);p.add_argument('--toolchain',type=pathlib.Path,required=True)
p.add_argument('--artifacts',type=pathlib.Path,required=True);p.add_argument('--census',type=pathlib.Path,required=True)
p.add_argument('--label',required=True);p.add_argument('--kind',choices=['key','yul','probe'],required=True);p.add_argument('--clean',action='store_true')
p.add_argument('--key-rules',type=pathlib.Path,help='KeY rules file, required for --kind key; no machine-specific default')
p.add_argument('--probe-source',action='append',default=[])
p.add_argument('--probe-output',action='append',default=[])
p.add_argument('--probe',nargs=argparse.REMAINDER)
a=p.parse_args()
if a.kind=='key' and (a.key_rules is None or not a.key_rules.is_file()):
    p.error('--kind key requires --key-rules pointing to an existing rules file')
root=a.root.resolve(); tool=a.toolchain.resolve(); artifacts=a.artifacts.resolve()
assert re.fullmatch(r'[a-zA-Z0-9_-]+',a.label)
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
subprocess.run(['git','status','--short'],cwd=root,check=True)
work=artifacts/a.label; work.mkdir(parents=True,exist_ok=True); build=work/'build'
if a.clean:
    if build.exists(): raise SystemExit('Refusing reused build directory: use a fresh label for clean comparison')
    build.mkdir()
config=(root/'lakefile.toml').read_text().replace('enableArtifactCache = true','enableArtifactCache = false')
config='moreLeanArgs = ["-j1", "-M12288"]\nbuildDir = '+json.dumps(str(build))+'\n'+config.replace('["--tstack=131072"]','["--tstack=131072", "-j1", "-M12288"]')
cfg=work/'lakefile.toml';cfg.write_text(config)
env=os.environ.copy();env['LEAN_NUM_THREADS']='1';env['PATH']=str(tool/'bin')+':'+env['PATH'];env['LAKE_ARTIFACT_CACHE']='false'
data=json.loads(a.census.read_text()); order=[] if a.kind=='probe' else data['keysort_order' if a.kind=='key' else 'build_order']
if a.kind=='probe' and (not a.probe or a.clean): raise SystemExit('probe requires --probe command and cannot claim a clean benchmark')
report=dict(repository=str(root),label=a.label,kind=a.kind,clean=a.clean,head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),census_sha256=hashlib.sha256(a.census.read_bytes()).hexdigest(),commands=[],status='running',reserve_bytes=4*1024**3,sampled_rss_budget_bytes=12*1024**3,guard_interval_seconds=.25,modules=[])
for binary in ['lean','lake']: report[binary]=subprocess.check_output([str(tool/'bin'/binary),'--version'],text=True).strip()
report['resources']={n:(pathlib.Path('/sys/fs/cgroup')/n).read_text().strip() for n in ['cpu.max','cpuset.cpus.effective','memory.max','memory.swap.max','memory.swap.current']}
report['swap_total_kib']=next(int(line.split()[1]) for line in pathlib.Path('/proc/meminfo').read_text().splitlines() if line.startswith('SwapTotal:'))
assert report['swap_total_kib']==0, 'No-swap prerequisite failed'
report['resource_policy']='min(host MemAvailable, cgroup headroom + clean active/inactive file minus kernel-style low-watermark allowance), v3'
report['resource_helper_sha256']=hashlib.sha256(pathlib.Path(__file__).with_name('resources.py').read_bytes()).hexdigest()
report['driver_sha256']=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
report['target_order_sha256']=hashlib.sha256(json.dumps(order).encode()).hexdigest()
report['config_policy_sha256']=hashlib.sha256(config.replace(str(build),'PRIVATE_BUILD_DIR').encode()).hexdigest()
report['config_sha256']=hashlib.sha256(cfg.read_bytes()).hexdigest()
report['resource_limit_note']='Inherited cgroup is hard cap; 12GiB RSS and 4GiB reserve are sampled guards, Lean -M12288 limits allocations.'
def file_hash(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()

probe_paths=[]
if a.kind=='probe':
    for name in a.probe_source+[x for x in a.probe if x.endswith('.lean')]:
        path=pathlib.Path(name)
        path=(root/path).resolve() if not path.is_absolute() else path.resolve()
        if not path.is_file(): raise SystemExit('Missing probe source '+str(path))
        if path not in probe_paths: probe_paths.append(path)
    if not probe_paths: raise SystemExit('Probe requires at least one --probe-source or .lean input')
report['source_check_scope']='census module sources; executed probe sources bound separately'
report['probe_sources_before']={str(p):file_hash(p) for p in probe_paths}
probe_outputs=[]
for name in a.probe_output:
    if a.kind!='probe':raise SystemExit('--probe-output requires probe mode')
    path=pathlib.Path(name)
    path=(root/path).resolve() if not path.is_absolute() else path.resolve()
    if path.exists():raise SystemExit('Probe output must be fresh: '+str(path))
    if path not in probe_outputs:probe_outputs.append(path)
report['probe_output_freshness_required']=True
report['probe_outputs_expected']=[str(p) for p in probe_outputs]
start=time.monotonic();peak=0;active=None

def save():
    report.update(wall_seconds=time.monotonic()-start,peak_process_group_rss_bytes=peak)
    (work/(a.kind+'-result.json')).write_text(json.dumps(report,indent=2)+'\n')

def cleanup():
    if report['status']=='running':
        report['status']='driver_error';save()
    if active is not None:
        try: os.killpg(active.pid,signal.SIGTERM)
        except ProcessLookupError: pass
        try: active.wait(timeout=5)
        except subprocess.TimeoutExpired:
            try: os.killpg(active.pid,signal.SIGKILL)
            except ProcessLookupError: pass
            active.wait()
atexit.register(cleanup)
def interrupted(signum, frame):
    report['status']='interrupted';report['signal']=signum;save();cleanup();raise SystemExit(128+signum)
for sig in [signal.SIGTERM, signal.SIGINT, signal.SIGHUP]: signal.signal(sig,interrupted)

def run(cmd,name):
    global peak,active
    before=time.monotonic(); top=0;why=None;stop_snapshot=None;min_available=None
    with (work/(a.kind+'.log')).open('a') as log:
        log.write(json.dumps(cmd)+'\n');log.flush()
        child=subprocess.Popen(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);active=child
        while child.poll() is None:
            rss=0
            for d in pathlib.Path('/proc').iterdir():
                if not d.name.isdigit():continue
                try:
                    stat=(d/'stat').read_text().rsplit(')',1)[1].split()
                    if int(stat[2])==child.pid: rss+=int(stat[21])*os.sysconf('SC_PAGE_SIZE')
                except (OSError,ValueError,IndexError):pass
            peak=max(peak,rss);top=max(top,rss)
            memory=snapshot()
            available=memory['available_estimate_bytes']
            min_available=available if min_available is None else min(min_available,available)
            if rss>12*1024**3 or available<4*1024**3:
                stop_snapshot=dict(memory,process_group_rss_bytes=rss)
                why='RESOURCE_STOP';os.killpg(child.pid,signal.SIGTERM)
                try:child.wait(timeout=5)
                except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL)
                break
            time.sleep(.25)
        code=child.wait();active=None
    entry=dict(module=name,command=cmd,exit=code,wall_seconds=time.monotonic()-before,peak_rss_bytes=top,stop=why,stop_snapshot=stop_snapshot,min_available_estimate_bytes=min_available)
    report['modules'].append(entry);save()
    print(json.dumps(entry),flush=True)
    if code or why:
        report['status']='fail';save();raise SystemExit(code if code>0 else 1)

def verify_sources(stage):
    changed=[row['path'] for row in data['modules'].values() if hashlib.sha256((root/row['path']).read_bytes()).hexdigest()!=row['sha256']]
    report['source_check_'+stage]=dict(status='fail' if changed else 'pass',changed=changed)
    if changed:
        report['status']='fail';save();raise SystemExit('Census/source mismatch: '+str(changed))

save()
verify_sources('before')
if a.kind=='probe': run(a.probe,'probe')
for module in order: run([str(tool/'bin/lake'),'-f',str(cfg),'--no-cache','build','+'+module],module)
if a.kind=='key':
    run([str(tool/'bin/lake'),'-f',str(cfg),'--no-cache','build','solkeycheck'],'solkeycheck-executable')
    rules=str(a.key_rules.resolve())
    report['keysort_rules_sha256']=hashlib.sha256(pathlib.Path(rules).read_bytes()).hexdigest()
    run([str(build/'bin/solkeycheck'),'--key',rules],'KeySort')
verify_sources('after')
report['probe_sources_after']={str(p):file_hash(p) for p in probe_paths}
if report['probe_sources_before']!=report['probe_sources_after']:
    report['status']='fail';save();raise SystemExit('Executed probe sources changed')
report['probe_outputs_after']={}
for path in probe_outputs:
    if not path.is_file():
        report['status']='fail';save();raise SystemExit('Missing fresh probe output: '+str(path))
    report['probe_outputs_after'][str(path)]={'sha256':file_hash(path),'bytes':path.stat().st_size}
report['status']='pass';save()
