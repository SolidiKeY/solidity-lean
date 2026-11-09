#!/usr/bin/env python3
"""Serial, cache-independent Lean closure build with resource and time evidence.
Fresh output required. Hold repository writer.lock around this process.
"""
import argparse, json, os, pathlib, resource, subprocess, sys, time
sys.dont_write_bytecode = True
from census import ROOT, census
p=argparse.ArgumentParser(); p.add_argument('lean',type=pathlib.Path); p.add_argument('output',type=pathlib.Path)
p.add_argument('--fixture',type=pathlib.Path,action='append'); a=p.parse_args()
a.lean=a.lean.resolve(); a.output=a.output.resolve(); a.output.mkdir(parents=True,exist_ok=False)
env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(a.output),LEAN_ABORT_ON_PANIC='1')
env.pop('LEAN_SRC_PATH',None)
cg=pathlib.Path('/sys/fs/cgroup')
if int((cg/'memory.swap.current').read_text()) != 0: raise SystemExit('SWAP_IN_USE')
report={'cgroup_memory_max':(cg/'memory.max').read_text().strip(),'swap_current':(cg/'memory.swap.current').read_text().strip(),'lean':str(a.lean),'versions':{},'settings':{'j':1,'lean_memory_mib':10000,'rss_cap_mib':12288,'reserve_mib':4096,'timeout_seconds':300,'clean_output':True,'artifact_cache':False},'modules':[]}
for tool in ('lean','lake'):
    report['versions'][tool]=subprocess.check_output([str(a.lean.parent/tool),'--version'],text=True).strip()
snapshot=census()
if not all(snapshot['closure_matches_base'].values()): raise SystemExit('UNAPPROVED_CLOSURE_SOURCE_DRIFT')
report['closure_source_hashes']=snapshot['closure_source_hashes']
modules=snapshot['topological_closure']
if a.fixture: modules += [str(x) for x in a.fixture]
started=time.monotonic()
for module in modules:
    fixture=module.endswith('.lean')
    src=ROOT/module if fixture else ROOT/(module.replace('.','/')+'.lean')
    out=a.output/((pathlib.Path(module).stem if fixture else module.replace('.','/'))+'.olean'); out.parent.mkdir(parents=True,exist_ok=True)
    log=a.output/((pathlib.Path(module).stem if fixture else module.replace('.','_'))+'.log')
    cmd=[str(a.lean),'-j1','-M10000','--tstack=131072','--root='+str(ROOT),'-o',str(out),str(src)]
    before=resource.getrusage(resource.RUSAGE_CHILDREN); t=time.monotonic(); peak=0; stop=None
    with log.open('w') as f:
        child=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
        while child.poll() is None:
            try:
                status=pathlib.Path('/proc',str(child.pid),'status').read_text()
                rss=int(status.split('VmRSS:')[1].split()[0]); peak=max(peak,rss)
                available=int(pathlib.Path('/proc/meminfo').read_text().split('MemAvailable:')[1].split()[0])
                limit=(cg/'memory.max').read_text().strip()
                if limit != 'max': available=min(available,(int(limit)-int((cg/'memory.current').read_text()))//1024)
                if int((cg/'memory.swap.current').read_text()): stop='SWAP_IN_USE'
                if rss>12288*1024: stop='RSS_CAP'
                if available<4096*1024: stop='HEADROOM'
                if time.monotonic()-t>300: stop='TIMEOUT'
                if stop: os.killpg(child.pid,9); break
            except (FileNotFoundError,IndexError): pass
            time.sleep(.05)
        code=child.wait()
    after=resource.getrusage(resource.RUSAGE_CHILDREN)
    row={'module':module,'command':cmd,'exit':code,'wall_seconds':time.monotonic()-t,'sampled_peak_rss_kib':peak,'run_children_high_water_rss_kib':after.ru_maxrss,'cpu_seconds':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,'stop':stop,'log':str(log)}
    report['modules'].append(row); print(json.dumps(row),flush=True)
    if code: break
report['closure_wall_seconds']=sum(x['wall_seconds'] for x in report['modules'] if not x['module'].endswith('.lean'))
report['wall_seconds']=time.monotonic()-started
report['pass']=len(report['modules'])==len(modules) and all(x['exit']==0 for x in report['modules'])
(a.output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
raise SystemExit(0 if report['pass'] else 1)
