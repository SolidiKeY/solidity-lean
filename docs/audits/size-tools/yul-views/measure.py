#!/usr/bin/env python3
"""Reproduce the frozen Yul view pilot; write evidence outside the code tree.
Needs pinned Lean/Lake, Linux wait4, fetched Lake cache, ~12 GiB free disk.
No network unless --fetch-cache. Takes the repository writer lock.
"""
import resource
import argparse, fcntl, hashlib, json, os, pathlib, re, statistics, subprocess, time
BASE='772806909ec30c93a85a95c01130a70b6bcc83ca'
NAMES=['AggregateMemoryWords','MemberArray','MemberArrayControls',
       'ArrayWordStore','ArrayWordStoreControls','ArrayWordHeap','ArrayWordHeapControls',
       'ArrayWordRetained','ArrayWordRetainedControls','StructWordStore','StructWordStoreControls',
       'StructWordHeap','StructWordHeapControls','StructWordRetained','StructWordRetainedControls']
FILES=['Solidity/Yul/Views/'+n+'.lean' for n in NAMES]

def run(cmd,cwd,log,env):
    mem=dict((k,int(v.split()[0])) for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()))
    assert mem['SwapTotal']==0 and mem['MemAvailable']>2*1024*1024, 'swap/headroom guard'
    def bounds(): resource.setrlimit(resource.RLIMIT_AS,(14*1024**3,14*1024**3))
    with open(log,'w') as out:
        start=time.perf_counter()
        child=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT,preexec_fn=bounds)
        _,status,usage=os.wait4(child.pid,0)
        child.returncode=os.waitstatus_to_exitcode(status)
        seconds=time.perf_counter()-start
    if child.returncode: raise RuntimeError(f'{cmd} failed ({child.returncode}): {log}')
    return seconds,usage.ru_maxrss

def decls(s):
    # These selected modules use line-start explicit declarations and ordinary
    # nested block comments; fail on duplicate declarations or unsupported syntax.
    masked=list(s); depth=0; i=0
    while i<len(s):
        if s[i:i+2]=='/-': depth+=1; masked[i:i+2]='  '; i+=2; continue
        if depth and s[i:i+2]=='-/': depth-=1; masked[i:i+2]='  '; i+=2; continue
        if depth: masked[i]='\n' if s[i]=='\n' else ' '
        i+=1
    assert depth==0
    m=''.join(masked)
    starts=list(re.finditer(r'^(theorem|def|abbrev|inductive|structure|namespace|end|open)\b[^\n]*',m,re.M))
    ns=[]; out={}
    for k,x in enumerate(starts):
        line=x.group(); kind=x[1]; end=starts[k+1].start() if k+1<len(starts) else len(m)
        if kind=='namespace': ns.append(line.split()[1]); continue
        if kind=='end':
            if ns: ns.pop()
            continue
        if kind=='open': continue
        name='.'.join(ns+[line.split()[1]])
        chunk=m[x.start():end].strip()
        if kind=='theorem':
            # The `:= by` terminator follows any let-expressions in the type.
            marker=chunk.find(':= by')
            if marker<0: marker=chunk.find(':=')
            assert marker>=0, name
            chunk=chunk[:marker].strip()
        assert name not in out,name
        out[name]=(kind,chunk)
    return out

def inventory(root):
    fs=list((root/'Solidity/Yul/Views').rglob('*.lean'))
    cs=[p for p in fs if p.stem.endswith('Controls')]
    return dict(files=len(fs),lines=sum(len(p.read_text().splitlines()) for p in fs),
                controls_files=len(cs),controls_lines=sum(len(p.read_text().splitlines()) for p in cs))

def snapshot(root):
    return {f:dict(lines=len((root/f).read_text().splitlines()),decls=decls((root/f).read_text()),preludes=(root/f).read_text().count('  first | (simp only;done) | decide | omega | rfl | skip\n')) for f in FILES}

def wrapper_lines(root):
    s=(root/'Solidity/Yul/Views/ArrayWordStore.lean').read_text()
    return len(s[s.index('theorem word_read'):s.index('theorem header')].strip().splitlines())


def audit_source(before,after):
    names=[]
    for f,b in before.items():
        a=after[f]
        for n,v in b['decls'].items():
            assert a['decls'].get(n)==v, f'changed declaration/type/definition: {f}:{n}'
            names.append(n)
    return names

def kernel_audit(root,names,out,env):
    path=root/'YulViewsTypeAudit.lean'
    path.write_text('import Lean\n'+''.join('import '+f[:-5].replace('/','.')+'\n' for f in FILES)+
      '\nrun_cmd do\n  let env ← Lean.getEnv\n'+''.join(
       '  match env.find? `'+n+' with\n  | none => throwError "missing '+n+'"\n  | some ci => Lean.logInfo ("TYPE '+n+' " ++ reprStr (ci.levelParams, ci.type))\n' for n in names)+
      '\n'+''.join('#print axioms '+n+'\n' for n in names))
    try: run(['lake','env','lean','-j1','--tstack=131072',str(path)],root,out,env)
    finally: path.unlink(missing_ok=True)
    text=out.read_text(); assert 'sorryAx' not in text
    return text

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=pathlib.Path,default=pathlib.Path.cwd())
    ap.add_argument('--worktree',type=pathlib.Path,required=True)
    ap.add_argument('--out',type=pathlib.Path,required=True)
    ap.add_argument('--patch',type=pathlib.Path,default=pathlib.Path(__file__).with_name('pilot.patch'))
    ap.add_argument('--samples',type=int,default=3)
    ap.add_argument('--fetch-cache',action='store_true')
    ap.add_argument('--static-only',action='store_true')
    a=ap.parse_args(); assert a.samples>0
    repo=a.repo.resolve(); wt=a.worktree.resolve(); out=a.out.resolve(); patch=a.patch.resolve()
    assert not wt.exists(), 'use a fresh worktree; existing work is never reset'
    assert not out.is_relative_to(repo), 'evidence must stay outside the code checkout'
    out.mkdir(parents=True,exist_ok=True)
    env=dict(os.environ,LEAN_NUM_THREADS='1')
    lock=pathlib.Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock');lock.parent.mkdir(exist_ok=True)
    with lock.open('a') as handle:
      fcntl.flock(handle,fcntl.LOCK_EX)
      run(['git','worktree','add','--detach',str(wt),BASE],repo,out/'setup.log',env)
      before=snapshot(wt); area=inventory(wt); before_wrapper=wrapper_lines(wt)
      if a.fetch_cache: run(['bash','scripts/ci/fetch-lake-cache.sh'],wt,out/'cache.log',env)
      timings={}; audits={}
      baseline_names=[n for f in FILES for n in before[f]['decls']]
      for phase in ['before','after']:
        if phase=='after':
          run(['git','apply','--check',str(patch)],wt,out/'apply-check.log',env)
          run(['git','apply',str(patch)],wt,out/'apply.log',env)
          after=snapshot(wt); audit_source(before,after)
          changed=subprocess.check_output(['git','diff','--name-only'],cwd=wt,text=True).splitlines()
          assert set(changed)<=set(FILES)
          for f in changed:
            diff=subprocess.check_output(['git','diff','--unified=0','--',f],cwd=wt,text=True)
            added='\n'.join(l[1:] for l in diff.splitlines() if l.startswith('+') and not l.startswith('+++'))
            assert not re.search(r'\b(sorry|native_decide|axiom|maxHeartbeats)\b',added)
        if a.static_only: continue
        # Build the exact slice closure, then materialize fetched artifacts.
        run(['lake','build']+[f[:-5].replace('/','.') for f in FILES],wt,out/(phase+'-build.log'),env)
        cache=env.get('LAKE_CACHE_DIR')
        if not cache:
          lean=pathlib.Path(subprocess.check_output(['which','lean'],env=env,text=True).strip()).resolve()
          cache=str(lean.parent.parent/'lake/cache')
        env['LAKE_CACHE_DIR']=cache
        run(['python3','scripts/ci/restore-lake-artifacts.py'],wt,out/(phase+'-restore.log'),env)
        timings[phase]={}
        for f in FILES:
          rows=[]
          for i in range(a.samples):
            tag=f'{phase}-{pathlib.Path(f).stem}-{i}'
            t=out/(tag+'.time')
            # Same emitted-output workload in both phases; imports already built.
            target=wt/'.lake/build/lib/lean'/pathlib.Path(f).with_suffix('.olean')
            seconds,kib=run(['lake','env','lean','-j1','--tstack=131072',f,'-o',str(target)],wt,out/(tag+'.log'),env)
            t.write_text(f'{seconds} {kib}\n')
            rows.append(dict(seconds=seconds,peak_rss_kib=int(kib)))
          timings[phase][f]=dict(samples=rows,median_seconds=statistics.median(x['seconds'] for x in rows),peak_rss_kib=max(x['peak_rss_kib'] for x in rows))
        audits[phase]=kernel_audit(wt,baseline_names,out/(phase+'-types-axioms.log'),env)
      if not a.static_only:
        assert audits['before']==audits['after'], 'kernel type/universe/axiom export changed'
        new_names=[n for f in FILES for n in after[f]['decls'] if n not in before[f]['decls']]
        new_audit=kernel_audit(wt,new_names,out/'new-types-axioms.log',env)
        for group in re.findall(r'depends on axioms: \[(.*?)\]',new_audit,re.S):
          assert set(x.strip() for x in group.split(','))<={'propext','Classical.choice','Quot.sound'}, group

      result=dict(base=BASE,patch_sha256=hashlib.sha256(patch.read_bytes()).hexdigest(),area=area,
        files=[dict(path=f,before_lines=before[f]['lines'],after_lines=after[f]['lines'],before_declarations=len(before[f]['decls']),after_declarations=len(after[f]['decls'])) for f in FILES],
        before_lines=sum(x['lines'] for x in before.values()),after_lines=sum(x['lines'] for x in after.values()),
        before_declarations=sum(len(x['decls']) for x in before.values()),after_declarations=sum(len(x['decls']) for x in after.values()),
        existing_declarations_checked=len(baseline_names),timings=timings,static_only=a.static_only,
        toolchain=subprocess.check_output(['lean','--version'],env=env,text=True).strip() if not a.static_only else None,
        limitations='no systemd scope on the cloud VM (H232); warm-import per-file elaboration, not a full build or physical execution')
      growth=after[FILES[0]]['lines']-before[FILES[0]]['lines']
      wrapper_growth=wrapper_lines(wt)-before_wrapper
      removed=sum(x['preludes'] for x in before.values())-sum(x['preludes'] for x in after.values())
      # The old word_read prelude is already charged inside wrapper_growth.
      prelude_saving=removed-1
      decoder_saving=before[FILES[1]]['lines']-after[FILES[1]]['lines']
      nonlayout=result['before_lines']-result['after_lines']+growth+wrapper_growth
      result['attribution']=dict(layout_kernel_growth=growth,layout_wrapper_growth=wrapper_growth,
          nonlayout_saving=nonlayout,prelude_saving=prelude_saving,decoder_saving=decoder_saving,
          support_saving=nonlayout-prelude_saving-decoder_saving)
      if timings:
        result['totals']={p:dict(sum_median_seconds=sum(v['median_seconds'] for v in rows.values()),peak_rss_kib=max(v['peak_rss_kib'] for v in rows.values())) for p,rows in timings.items()}
      (out/'measurement.json').write_text(json.dumps(result,indent=2)+'\n')
      print(json.dumps({k:v for k,v in result.items() if k not in ['files','timings']},indent=2))
      print('worktree retained:',wt)
if __name__=='__main__': main()
