#!/usr/bin/env python3
"""Serial measured sample, dependency cache only (never build cold imports).
Run from repository root with Lean/Lake/elan on PATH:
python3 docs/audits/direction-tools/timing/measure.py --repo /absolute/clean/checkout --work /absolute/external/dir [--profiles]
External logs contain full profiler output; small result JSON is in --work.
The caller MUST hold the shared writer lock. No Lean sources are written.
"""
import argparse,json,os,pathlib,re,signal,subprocess,time
HERE=pathlib.Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def command(args,cwd,log,timeout=600):
    start=time.monotonic(); peak=0; reason=None
    with log.open('w') as f:
        proc=subprocess.Popen(args,cwd=cwd,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
        while proc.poll() is None:
            # Conservative summed RSS of this command process group, including
            # shared pages; stop at 12 GiB or below 3 GiB available OS memory.
            rss=0
            for entry in pathlib.Path('/proc').iterdir():
                if not entry.name.isdigit(): continue
                try:
                    if os.getpgid(int(entry.name))!=proc.pid: continue
                    status=(entry/'status').read_text()
                    match=re.search(r'^VmRSS:\s+(\d+)',status,re.M)
                    if match: rss+=int(match.group(1))
                except (OSError,ProcessLookupError): pass
            peak=max(peak,rss)
            available=int(re.search(r'MemAvailable:\s+(\d+)',pathlib.Path('/proc/meminfo').read_text())[1])
            if time.monotonic()-start>timeout: reason='timeout'
            elif rss>12*1024**2 or available<3*1024**2: reason='memory_guard'
            if reason:
                try: os.killpg(proc.pid,signal.SIGTERM)
                except ProcessLookupError: pass
                try: proc.wait(timeout=5)
                except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL); proc.wait()
                break
            try: proc.wait(timeout=0.1)
            except subprocess.TimeoutExpired: pass
        code=proc.wait() if reason is None else (124 if reason=='timeout' else 125)
    return {'command':args,'cwd':str(cwd),'exit_code':code,'wall_seconds':time.monotonic()-start,'peak_sampled_group_rss_kib':peak,'stop_reason':reason,'log':str(log)}
def main():
    global ROOT
    ap=argparse.ArgumentParser(); ap.add_argument('--profiles',action='store_true'); ap.add_argument('--repo',type=pathlib.Path,required=True); ap.add_argument('--work',type=pathlib.Path,required=True); args=ap.parse_args(); ROOT=args.repo.resolve(); args.work.mkdir(parents=True,exist_ok=True)
    assert subprocess.check_output(['git','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip()=='d6fd95f0886775d7c286813fa9b993a40ba7a777'
    assert not subprocess.check_output(['git','-C',str(ROOT),'status','--porcelain','--untracked-files=no'],text=True).strip(), 'dirty measured source'
    data=json.loads((HERE/'inventory.json').read_text()); results=[]
    saved=args.work/'sample-results.json'
    previous={r['path']:r for r in json.loads(saved.read_text())['samples']} if saved.exists() else {}
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
        p=row['path']; bridge=p.startswith('Bridge/'); cwd=ROOT/'Bridge' if bridge else ROOT
        file=p.removeprefix('Bridge/') if bridge else p
        module=file.removesuffix('.lean').replace('/','.')
        item={**previous.get(p,{}),**row,'module':module,'toolchain':versions['lean']}
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
        results.append(item)
        (args.work/'sample-results.json').write_text(json.dumps({'base':data['base'],'versions':versions,'KeySort':key,'conditions':'one worker, -j1, LEAN_NUM_THREADS=1, cache-only dependencies, no systemd scope on the cloud VM (H232); plain run before profiled run; one observation, OS page cache uncontrolled','samples':results},indent=2)+'\n')
        print(i,p,item['status'],flush=True)
if __name__=='__main__': main()
