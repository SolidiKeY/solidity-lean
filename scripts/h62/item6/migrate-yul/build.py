#!/usr/bin/env python3
"""Serial clean Lake module build with private per-toolchain artifacts and RSS guard.
No source/config/toolchain writes in the checkout; no shared/master cache.
"""
import atexit, argparse, fcntl, hashlib, json, os, pathlib, re, signal, subprocess, time
p=argparse.ArgumentParser()
p.add_argument('--root',type=pathlib.Path,required=True);p.add_argument('--toolchain',type=pathlib.Path,required=True)
p.add_argument('--artifacts',type=pathlib.Path,required=True);p.add_argument('--census',type=pathlib.Path,required=True)
p.add_argument('--label',required=True);p.add_argument('--kind',choices=['key','yul'],required=True);p.add_argument('--clean',action='store_true')
a=p.parse_args(); root=a.root.resolve(); tool=a.toolchain.resolve(); artifacts=a.artifacts.resolve()
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
data=json.loads(a.census.read_text()); order=data['keysort_order' if a.kind=='key' else 'build_order']
report=dict(label=a.label,kind=a.kind,clean=a.clean,head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),census_sha256=hashlib.sha256(a.census.read_bytes()).hexdigest(),commands=[],status='running',reserve_bytes=4*1024**3,sampled_rss_budget_bytes=12*1024**3,guard_interval_seconds=.25,modules=[])
for binary in ['lean','lake']: report[binary]=subprocess.check_output([str(tool/'bin'/binary),'--version'],text=True).strip()
report['resources']={n:(pathlib.Path('/sys/fs/cgroup')/n).read_text().strip() for n in ['cpu.max','cpuset.cpus.effective','memory.max','memory.swap.max','memory.swap.current']}
report['swap_total_kib']=next(int(line.split()[1]) for line in pathlib.Path('/proc/meminfo').read_text().splitlines() if line.startswith('SwapTotal:'))
assert report['swap_total_kib']==0, 'No-swap prerequisite failed'
report['driver_sha256']=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
report['target_order_sha256']=hashlib.sha256(json.dumps(order).encode()).hexdigest()
report['config_policy_sha256']=hashlib.sha256(config.replace(str(build),'PRIVATE_BUILD_DIR').encode()).hexdigest()
report['config_sha256']=hashlib.sha256(cfg.read_bytes()).hexdigest()
report['resource_limit_note']='Inherited cgroup is hard cap; 12GiB RSS and 4GiB reserve are sampled guards, Lean -M12288 limits allocations.'
start=time.monotonic();peak=0;active=None

def save():
    report.update(wall_seconds=time.monotonic()-start,peak_process_group_rss_bytes=peak)
    (work/(a.kind+'-result.json')).write_text(json.dumps(report,indent=2)+'\n')

def cleanup():
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
    before=time.monotonic(); top=0;why=None
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
            cg=pathlib.Path('/sys/fs/cgroup');cap=int((cg/'memory.max').read_text());used=int((cg/'memory.current').read_text())
            if rss>12*1024**3 or cap-used<4*1024**3:
                why='RESOURCE_STOP';os.killpg(child.pid,signal.SIGTERM)
                try:child.wait(timeout=5)
                except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL)
                break
            time.sleep(.25)
        code=child.wait();active=None
    entry=dict(module=name,command=cmd,exit=code,wall_seconds=time.monotonic()-before,peak_rss_bytes=top,stop=why)
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
for module in order: run([str(tool/'bin/lake'),'-f',str(cfg),'--no-cache','build','+'+module],module)
if a.kind=='key':
    run([str(tool/'bin/lake'),'-f',str(cfg),'--no-cache','build','solkeycheck'],'solkeycheck-executable')
    rules='/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key'
    report['keysort_rules_sha256']=hashlib.sha256(pathlib.Path(rules).read_bytes()).hexdigest()
    run([str(build/'bin/solkeycheck'),'--key',rules],'KeySort')
verify_sources('after')
report['status']='pass';save()
