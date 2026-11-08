#!/usr/bin/env python3
"""Pinned serial reference build and matched per-module checks; stdlib only.
Caller holds writer lock; run with Lean/elan/Lake on PATH:
python3 .../references.py --cloud-vm --project EvmYul --refs EXTERNAL --work EXTERNAL/evmyul-times
Mathlib cache is attempted first; a failed cache is explicit. Reference dependency
compilation is prep, never attributed to project-only module check time.
"""
import argparse,importlib.util,json,pathlib,re,subprocess,sys
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent
PINS={'EvmYul':'047f63070309f436b66c61e276ab3b6d1169265a','Clear':'6ef2e7eda01080e5d5fd7474354c1a71adab5071'}
REPOS={'EvmYul':'NethermindEth/EVMYulLean','Clear':'NethermindEth/Clear'}
def load(name):
    spec=importlib.util.spec_from_file_location(name,HERE/(name+'.py')); mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--cloud-vm',action='store_true'); ap.add_argument('--project',choices=PINS,required=True); ap.add_argument('--refs',type=pathlib.Path,required=True); ap.add_argument('--work',type=pathlib.Path,required=True); args=ap.parse_args()
    if not args.cloud_vm: ap.error('explicit --cloud-vm required under H232; host execution unsupported')
    meter=load('measure'); meter.CLOUD_VM_OPT_IN=True; audit=load('audit'); args.refs=args.refs.resolve(); args.refs.mkdir(parents=True,exist_ok=True); args.work=args.work.resolve(); args.work.mkdir(parents=True,exist_ok=True)
    root=args.refs/args.project
    def run(cmd,name,timeout=1800,cwd=None): return meter.command(cmd,cwd or root,args.work/(name+'.log'),timeout)
    def git(*cmd): return subprocess.check_output(['git','-C',str(root),*cmd],text=True).strip()
    if not root.exists():
        r=meter.command(['git','clone','--depth','1','https://github.com/'+REPOS[args.project]+'.git',str(root)],args.refs,args.work/'clone.log')
        if r['exit_code']: raise SystemExit('reference clone failed')
        run(['git','fetch','--depth','1','origin',PINS[args.project]],'pin-fetch'); run(['git','checkout','--detach',PINS[args.project]],'pin-checkout')
    assert git('rev-parse','HEAD')==PINS[args.project], 'reference pin mismatch'
    assert not git('status','--porcelain','--untracked-files=no'), 'dirty reference source'
    statefile=args.work/'reference-results.json'
    state=json.loads(statefile.read_text()) if statefile.exists() else {'project':args.project,'pin':PINS[args.project],'source':str(root),'preparation':[],'build_attempts':[],'modules':[]}
    assert state['pin']==PINS[args.project] and state['source']==str(root)
    def save(): statefile.write_text(json.dumps(state,indent=2)+'\n')
    for tool in ['lean','lake']:
        r=run([tool,'--version'],tool+'-version',60); observed=(args.work/(tool+'-version.log')).read_text().strip(); assert r['exit_code']==0
        if tool+'_version' in state: assert state[tool+'_version']==observed, 'resume toolchain mismatch'
        state[tool+'_version']=observed
    manifest=json.loads((root/'lake-manifest.json').read_text()); pkgdir=root/manifest.get('packagesDir','.lake/packages'); pkgdir.mkdir(parents=True,exist_ok=True)
    if not state.get('dependencies_prepared'):
        for package in manifest['packages']:
            dest=pkgdir/package['name']; rev=package['rev']
            if not dest.exists():
                r=run(['git','clone','--depth','1',package['url'],str(dest)],'dep-'+package['name']+'-clone',600)
                state['preparation'].append(r); save()
                if r['exit_code']: raise SystemExit('dependency clone failed: '+package['name'])
            assert not subprocess.check_output(['git','-C',str(dest),'status','--porcelain','--untracked-files=no'],text=True).strip(), 'dirty dependency: '+package['name']
            actual=subprocess.check_output(['git','-C',str(dest),'rev-parse','HEAD'],text=True).strip()
            if actual!=rev:
                for label,cmd in [('fetch',['git','fetch','--depth','1','origin',rev]),('checkout',['git','checkout','--detach',rev])]:
                    r=run(cmd,'dep-'+package['name']+'-'+label,600,dest); state['preparation'].append(r); save()
                    if r['exit_code']: raise SystemExit('dependency pin failed: '+package['name'])
            assert subprocess.check_output(['git','-C',str(dest),'rev-parse','HEAD'],text=True).strip()==rev
        state['dependencies_prepared']=True; save()
    def verify_dependencies():
        for package in manifest['packages']:
            dest=pkgdir/package['name']
            assert subprocess.check_output(['git','-C',str(dest),'rev-parse','HEAD'],text=True).strip()==package['rev'], 'dependency pin mismatch: '+package['name']
            assert not subprocess.check_output(['git','-C',str(dest),'status','--porcelain','--untracked-files=no'],text=True).strip(), 'dirty dependency: '+package['name']
    verify_dependencies()
    if 'cache' not in state:
        state['cache']=run(['lake','exe','cache','get'],'dependency-cache',1800); save()
    if not state['build_attempts'] or state['build_attempts'][-1]['exit_code']:
        r=run(['lake','build','EvmYul' if args.project=='EvmYul' else 'Main'],'build-'+str(len(state['build_attempts'])),1800)
        state['build_attempts'].append(r); save()
        if r['exit_code']: raise SystemExit('reference build failed; retained failure and partial artifacts')
    assert not git('status','--porcelain','--untracked-files=no'), 'build changed tracked reference source'
    verify_dependencies()
    paths=git('ls-files','*.lean').splitlines(); graph={}; info={}
    for p in paths:
        text=(root/p).read_text(); mod=p[:-5].replace('/','.'); clean=audit.strip_comments(text)
        imports=[]
        for line in clean.splitlines():
            line=line.strip()
            if not line or line in ('prelude','module'): continue
            m=re.match(r'(?:(?:public|meta)\s+)*import\s+(.+)',line)
            if not m: break
            imports+=m[1].split()
        graph[mod]=imports
        isgen=args.project=='Clear' and p.startswith('Generated/') and not p.endswith('_user.lean')
        info[mod]={'path':p,'lines':len(text.splitlines()),'classification':'detected_generated' if isgen else 'unmarked_not_proven_handwritten'}
    seen=set(); order=[]
    def visit(mod):
        if mod in seen or mod not in graph: return
        seen.add(mod)
        for dep in graph[mod]: visit(dep)
        order.append(mod)
    visit('EvmYul' if args.project=='EvmYul' else 'Main')
    state['tracked_lean_lines']=sum(r['lines'] for r in info.values()); state['built_closure_lines']=sum(info[m]['lines'] for m in order); state['built_closure_modules']=len(order)
    state['measurement_boundary']='project modules in default library import closure; warm dependency oleans, separate lake env lean -j1 invocation per module; physical lines; build attempts include preparation dependencies and are not matched module costs'
    prior={r['module']:r for r in state['modules']}
    for i,mod in enumerate(order):
        if mod in prior and prior[mod]['check']['exit_code']==0: continue
        row={'module':mod,**info[mod]}; row['check']=run(['lake','env','lean','-j1','--tstack=131072','-DautoImplicit=false',row['path']],'module-'+str(i),600)
        state['modules']=[r for r in state['modules'] if r['module']!=mod]+[row]; save(); print(mod,row['check']['exit_code'],flush=True)
    state['status']='pass' if all(r['check']['exit_code']==0 for r in state['modules']) and len(state['modules'])==len(order) else 'fail'; save()
    print(state['status'],args.project,flush=True)
if __name__=='__main__': main()
