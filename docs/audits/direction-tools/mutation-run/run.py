#!/usr/bin/env python3
"""Pinned, serial, first-kill mutation experiment. Python standard library only.
Run: PATH="$HOME/.elan/bin:$PATH" python3 -B docs/audits/direction-tools/mutation-run/run.py --work /workspace/da-mutation-runtime/run
Only scratch worktree source is mutated. Surviving means surviving the recorded
selected dependent slice, not all repository theorems. Baseline must pass first.
"""
import argparse, collections, fcntl, hashlib, json, os, pathlib, re, resource, subprocess, time
BASE='d6fd95f0886775d7c286813fa9b993a40ba7a777'
HERE=pathlib.Path(__file__).resolve().parent
ROOT=pathlib.Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
def git(*a): return subprocess.check_output(['git',*a],cwd=ROOT,text=True)
def source(p): return git('show',BASE+':'+p)
def module(p): return p[:-5].replace('/','.')
def dump(p,x): p.write_text(json.dumps(x,indent=2)+'\n')
def catalogue():
    ms=[]
    for m in json.loads(source('docs/audits/direction-tools/mutation/mutants.json')):
        m={k:m[k] for k in ('id','path','line','old','new','definition')}
        m['targets']=['Solidity/Optimizer/Simplify.lean','Solidity/Examples/Tactics/Operators.lean','Solidity/Examples/Tactics/Values.lean','Solidity/Examples/Tactics/SignedCasts.lean','Solidity/Examples/Tactics/ModularArithmetic.lean'] if m['path'].endswith('Ops.lean') else [m['path']]
        # Expensive dependent slices are explicit, never inferred from lexical mentions.
        ms.append(m)
    def add(p,old,new,targets,desc):
        s=source(p); assert s.count(old)==1,(p,old,s.count(old))
        ms.append(dict(id='M%02d'%(len(ms)+1),path=p,line=s[:s.index(old)].count('\n')+1,old=old,new=new,definition=desc,targets=targets))
    p='Solidity/Evm/Machine.lean'
    add(p,'def H : Nat := 2 ^ 255','def H : Nat := 2 ^ 254',[p],'signed word threshold')
    add(p,'| .root o, i => .root (o + i)','| .root o, i => .root (o + i + 1)',['Solidity/Evm/Layout.lean'],'root slot offset')
    p='Solidity/Backend/Scalar/Checked.lean'
    add(p,'.op .ADD,\n   .op (.DUP ⟨1, by decide⟩), .op .GT]','.op .SUB,\n   .op (.DUP ⟨1, by decide⟩), .op .GT]',[p],'overflow-test arithmetic')
    add(p,'.op (.DUP ⟨1, by decide⟩), .op .LT]','.op (.DUP ⟨1, by decide⟩), .op .GT]',[p],'underflow-test comparison')
    p='Solidity/Yul/Words.lean'
    add(p,'if (xs 1).val = 0 then word 0 else word ((xs 0).val % (xs 1).val)','if (xs 1).val = 0 then word 1 else word ((xs 0).val % (xs 1).val)',['Solidity/Yul/WordLaws.lean'],'modulo zero divisor')
    add(p,'if (xs 0).val ≥ 256 then word 0 else word ((xs 1).val <<< (xs 0).val)','if (xs 0).val ≥ 256 then word 1 else word ((xs 1).val <<< (xs 0).val)',['Solidity/Yul/WordLaws.lean'],'large shift result')
    p='Solidity/Lowering/V07/WordCasts.lean'
    add(p,'def signed : Source.IntTy := ⟨true,256,by decide⟩','def signed : Source.IntTy := ⟨true,128,by decide⟩',[p],'signed cast width')
    for m in ms:
        lines=source(m['path']).splitlines(); assert m['old'] in '\n'.join(lines[m['line']-1:]),m['id']
        m['source_sha256']=hashlib.sha256(source(m['path']).encode()).hexdigest()
        m['area']=m['path'].split('/')[1]
        m['generated']=False
        m['provenance']='unmarked source; not a historical handwritten-authorship claim'
        m['description']=m['definition']+': '+m['old']+' -> '+m['new']
    return ms

def failure_names(mod,out):
    lines=source(mod.replace('.','/')+'.lean').splitlines()
    declarations=[]
    for i,line in enumerate(lines,1):
        match=re.match(r'^(?:@\[[^]]+\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*(theorem|lemma|def|example)\b(?:\s+([^\s:(]+))?',line)
        if match: declarations.append((i,match[2] or 'anonymous '+match[1]))
    names=[]
    for match in re.finditer(r'\.lean:(\d+):\d+: error(?:\([^)]*\))?:',out):
        n=int(match[1]); previous=[d for d in declarations if d[0]<=n]
        names.append(mod+':'+str(n)+':'+(previous[-1][1] if previous else 'unattributed'))
    return sorted(set(names))

def main():
    a=argparse.ArgumentParser(); a.add_argument('--work',type=pathlib.Path); a.add_argument('--check',action='store_true'); a.add_argument('--refresh',action='store_true'); a.add_argument('--seconds',type=int,default=3600); a.add_argument('--timeout',type=int,default=240); args=a.parse_args()
    ms=catalogue()
    if args.refresh:
        rs=json.loads((HERE/'results.json').read_text())
        for r in rs:
            if r['verdict']=='KILLED': r['killed_by']=failure_names(r['checks'][-1]['module'],r['checks'][-1]['decisive_output'])
        dump(HERE/'results.json',rs); dump(HERE/'summary.json',summarize(ms,rs)); return
    if args.check:
        assert json.loads((HERE/'mutants.json').read_text())==ms
        rs=json.loads((HERE/'results.json').read_text()); assert len({r['id'] for r in rs})==len(rs)
        assert all(r['id'] in {m['id'] for m in ms} for r in rs)
        assert rs, 'no executed mutants'
        index={m['id']:m for m in ms}
        for r in rs:
            m=index[r['id']]
            assert all(r[k]==m[v] for k,v in [('file','path'),('line','line'),('area','area'),('description','description')])
            assert r['checks']
            assert r['baseline_pass'] or r['verdict']=='BLOCKED'
            if r['baseline_pass']: assert all(c['pristine']['returncode']==0 for c in r['checks'])
            assert r['seconds']==round(sum(c['seconds'] for c in r['checks']),3)
            assert r['checks'][0]['module']==module(m['path'])
            assert r['verdict'] in ['KILLED','SURVIVOR','BLOCKED']
            if r['verdict']=='SURVIVOR':
                assert all(c['returncode']==0 for c in r['checks'])
                assert set(map(module,m['targets'])) <= {c['module'] for c in r['checks']}
                assert not r['killed_by']
            elif r['verdict']=='KILLED':
                assert r['checks'][-1]['returncode']>0 and r['checks'][-1]['returncode']!=124
                assert r['killed_by'] and 'decisive_output' in r['checks'][-1]
            else: assert r['checks'][-1]['returncode']!=0
        assert (HERE/'results.json').stat().st_size<1000000
        assert json.loads((HERE/'summary.json').read_text())==summarize(ms,rs)
        print('PASS pinned catalogue, unique results, baseline guards, summary arithmetic'); return
    assert args.work and args.work.resolve()!=ROOT and not str(args.work.resolve()).startswith(str(ROOT)+'/')
    args.work.mkdir(parents=True,exist_ok=True)
    lock=pathlib.Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock'); lock.parent.mkdir(exist_ok=True)
    with lock.open('a') as f:
        fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
        assert not git('status','--porcelain','--untracked-files=no').strip()
        dump(HERE/'mutants.json',ms)
        tree=args.work/'tree'
        if not tree.exists(): subprocess.run(['git','worktree','add','--detach',str(tree),BASE],cwd=ROOT,check=True)
        assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=tree,text=True).strip()==BASE
        assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=tree,text=True).strip()
        # Shared cache metadata only. Direct imports use resolved content-addressed artifacts.
        if not (tree/'.lake').exists(): (tree/'.lake').symlink_to(ROOT/'.lake',target_is_directory=True)
        env=dict(os.environ,LEAN_NUM_THREADS='1')
        def limits(): resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
        def run(cmd,name,env=env):
            t=time.monotonic()
            try:
                r=subprocess.run(cmd,cwd=tree,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=args.timeout,preexec_fn=limits)
                out=r.stdout; rc=r.returncode
            except subprocess.TimeoutExpired as e: out=(e.stdout or b'').decode() if isinstance(e.stdout,bytes) else (e.stdout or ''); rc=124
            (args.work/(name+'.log')).write_text(out)
            return dict(returncode=rc,seconds=round(time.monotonic()-t,3),log=str(args.work/(name+'.log'))),out
        targets=sorted({module(p) for m in ms for p in [m['path']]+m['targets']})
        b,out=run(['lake','--no-build','build']+[t+':olean' for t in targets],'baseline')
        dump(args.work/'baseline.json',b)
        if b['returncode']: print('BASELINE_BLOCKED',b,flush=True); return
        # Parse pinned import graph; rebuild precisely the mutant-to-selected-target paths.
        paths=git('ls-tree','-r','--name-only',BASE).splitlines()
        texts={module(p):source(p) for p in paths if p.endswith('.lean') and p.startswith('Solidity/')}
        imports={m:re.findall(r'^import\s+([\w.]+)',s,re.M) for m,s in texts.items()}
        def deps(m):
            seen=set()
            def visit(x):
                if x in seen:return
                seen.add(x)
                for d in imports.get(x,[]):visit(d)
            visit(m); return seen
        allmods=set()
        for t in targets: allmods |= deps(t)
        allmods=sorted(allmods & texts.keys())
        q,out=run(['lake','--quiet','--no-build','query']+[t+':olean' for t in allmods],'artifact-query')
        artifacts=[pathlib.Path(l) for l in out.splitlines() if l.startswith('/') and l.endswith('.olean')]
        assert q['returncode']==0 and len(artifacts)==len(allmods),(q,len(artifacts),len(allmods))
        artifact_map=dict(zip(allmods,artifacts))
        overlay=args.work/'overlay'
        def seed():
            overlay.mkdir(exist_ok=True)
            for x in overlay.rglob('*.olean'): x.unlink()
            for mod,artifact in artifact_map.items():
                link=overlay/(mod.replace('.','/')+'.olean'); link.parent.mkdir(parents=True,exist_ok=True); link.symlink_to(artifact)
        seed()
        menv=dict(env,LEAN_PATH=str(overlay))
        pristine_overlay=args.work/'pristine-overlay'
        pristine_overlay.mkdir(exist_ok=True)
        for x in pristine_overlay.rglob('*.olean'):x.unlink()
        for mod,artifact in artifact_map.items():
            link=pristine_overlay/(mod.replace('.','/')+'.olean');link.parent.mkdir(parents=True,exist_ok=True);link.symlink_to(artifact)
        pristine_env=dict(env,LEAN_PATH=str(pristine_overlay)); pristine_pass={}
        rs=[]; start=time.monotonic()
        dump(HERE/'results.json',rs); dump(HERE/'summary.json',summarize(ms,rs))
        for m in sorted(ms,key=lambda m:(m['area']=='Semantics',m['id'])):
            if time.monotonic()-start>args.seconds:break
            p=tree/m['path']; original=source(m['path']); lines=original.splitlines(keepends=True)
            # All edits are exact at the pinned line, not global replacement.
            i=m['line']-1; tail=''.join(lines[i:]); assert m['old'] in tail
            p.write_text(''.join(lines[:i])+tail.replace(m['old'],m['new'],1))
            seed()
            changed=module(m['path']); wanted=set()
            for target in map(module,m['targets']): wanted |= {d for d in deps(target) if changed in deps(d)}
            wanted.add(changed); order=[]
            def visit(x):
                if x in order:return
                for d in imports.get(x,[]):
                    if d in wanted:visit(d)
                order.append(x)
            for x in map(module,m['targets']):visit(x)
            visit(changed)
            checks=[]; killed=[]; verdict='SURVIVOR'
            try:
                for mod in order:
                    if mod not in pristine_pass:
                        dest=args.work/'pristine'/(mod.replace('.','/')+'.olean'); dest.parent.mkdir(parents=True,exist_ok=True)
                        if mod==changed:p.write_text(original)
                        try:
                            c,out=run(['lean','-j1','--tstack=131072','-o',str(dest),mod.replace('.','/')+'.lean'],'pristine-'+mod,pristine_env)
                        finally:
                            if mod==changed:p.write_text(''.join(lines[:i])+tail.replace(m['old'],m['new'],1))
                        c['module']=mod
                        if c['returncode']:
                            c['decisive_output']=out[:12000];c['pristine_failure']=True;checks.append(c);verdict='BLOCKED';break
                        pristine_pass[mod]=c
                    dest=overlay/(mod.replace('.','/')+'.olean'); dest.parent.mkdir(parents=True,exist_ok=True)
                    if dest.exists() or dest.is_symlink(): dest.unlink()
                    c,out=run(['lean','-j1','--tstack=131072','-o',str(dest),mod.replace('.','/')+'.lean'],m['id']+'-'+mod,menv)
                    c['module']=mod; c['pristine']=pristine_pass[mod]; checks.append(c)
                    if c['returncode']:
                        verdict='KILLED' if c['returncode']>0 and c['returncode']!=124 and re.search(r'error(?:\([^)]*\))?:',out) and not any(e in out for e in ['unknown module prefix','object file','out of memory','stack overflow']) else 'BLOCKED'
                        c['decisive_output']=out[:12000]
                        for ln in out.splitlines():
                            match=re.match(r'.*?\.lean:(\d+):\d+: error(?:\([^)]*\))?:',ln)
                            if match:
                                n=int(match[1]); prefix=texts.get(mod,'').splitlines()[:n]
                                names=re.findall(r'^(?:@\[[^]]+\]\s*)?(?:private\s+)?(?:theorem|lemma|def|example)\s+([^\s:(]+)','\n'.join(prefix),re.M)
                                killed.append(mod+':'+str(n)+':'+(names[-1] if names else 'anonymous'))
                        break
            finally:p.write_text(original)
            rs.append(dict(id=m['id'],area=m['area'],file=m['path'],line=m['line'],description=m['description'],verdict=verdict,killed_by=failure_names(checks[-1]['module'],checks[-1]['decisive_output']) if verdict=='KILLED' else [],seconds=round(sum(c['seconds'] for c in checks),3),baseline_pass=all(c.get('pristine',{}).get('returncode')==0 for c in checks),checks=checks))
            dump(HERE/'results.json',rs); dump(HERE/'summary.json',summarize(ms,rs)); print(m['id'],verdict,rs[-1]['seconds'],killed[:2],flush=True)

def summarize(ms,rs):
    areas={}
    for area in sorted({m['area'] for m in ms}):
        rows=[r for r in rs if r['area']==area]; killed=sum(r['verdict']=='KILLED' for r in rows); survivors=sum(r['verdict']=='SURVIVOR' for r in rows)
        areas[area]=dict(candidates=sum(m['area']==area for m in ms),ran=len(rows),killed=killed,survivors=survivors,blocked=len(rows)-killed-survivors,score=killed/(killed+survivors) if killed+survivors else None)
    return dict(base=BASE,execution_order=[r['id'] for r in rs],score_label='sampled selected-dependent-slice mutation score, not area-wide assurance',complete_catalogue_executed=len(ms)==len(rs),candidates=len(ms),ran=len(rs),areas=areas,generated_candidates=0,unmarked_candidates=len(ms),survivors=[dict(id=r['id'],importance=1 if r['area'] in ['Semantics','Calculus'] else 2,meaning='No check in the recorded affected selected-dependent slice constrains this change; no whole-repository absence-of-proof claim.',description=r['description']) for r in rs if r['verdict']=='SURVIVOR'],boundary='Kernel elaboration of pinned source and selected dependent paths; first failure stops each mutant. Not external EVM/solc conformance, exhaustive dependency coverage, or a reference-class ratio.',limitations=['no systemd scope on the cloud VM (H232)','No full rebuild from scratch; published cache and baseline selected builds required.','Unmarked is not proven handwritten.','M31 strengthens/restricts a recognizer; survival can be vacuity rather than missing proof.'])
if __name__=='__main__':main()
