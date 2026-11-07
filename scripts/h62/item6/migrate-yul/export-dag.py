#!/usr/bin/env python3
"""Serial schema3 old-kernel inventory export, with original bounded driver.
The DAG representation retains every expression node and declaration.
"""
import sys
sys.dont_write_bytecode=True
import argparse,pathlib,json,re,shutil,subprocess
import interfaces
digest=interfaces.digest
def export_all(a):
    root=a.root.resolve();out=a.artifacts.resolve()/a.label
    if not re.fullmatch(r'[A-Za-z0-9_-]+',a.label):raise ValueError('invalid label')
    out.mkdir(parents=True,exist_ok=False);(out/'snapshots').mkdir()
    census=json.loads(a.census.read_text());mods=census['yul_modules']
    helper=root/'tests/h62/item6/migrate-yul/ExportInterfacesDag.lean'
    driver=root/'scripts/h62/item6/migrate-yul/build.py'
    tool=a.toolchain.resolve();lib=a.lib.resolve()
    manifest=dict(expression_schema=3,status='running',scope='persisted kernel declarations; source cases require prescribed builds',module_count=len(mods),census_sha256=digest(a.census),helper_sha256=digest(helper),wrapper_sha256=digest(__file__),parser_sha256=digest(interfaces.__file__),validator_sha256=digest(interfaces.expr_dag.__file__),modules=[])
    path=out/'manifest.json'
    def save():path.write_text(json.dumps(manifest,indent=2)+'\n')
    missing=[n for n in mods if not (lib/(n.replace('.','/')+'.olean')).is_file()]
    if missing:
        manifest.update(status='blocked',blocker='MISSING_BUILT_MODULES',missing=missing);save();raise ValueError('full interface export lacks '+str(len(missing))+' built modules')
    save()
    try:
        for i,n in enumerate(mods):
            if digest(helper)!=manifest['helper_sha256'] or digest(a.census)!=manifest['census_sha256'] or digest(interfaces.__file__)!=manifest['parser_sha256'] or digest(interfaces.expr_dag.__file__)!=manifest['validator_sha256']:raise ValueError('export inputs changed')
            if shutil.disk_usage(out).free<4*1024**3:raise ValueError('disk reserve below4GiB')
            base=lib/(n.replace('.','/')+'.olean')
            sources=[base]+[pathlib.Path(str(base)+suffix) for suffix in ['.private','.server'] if pathlib.Path(str(base)+suffix).exists()]
            label=f'module-{i:04d}';raw=out/'snapshots'/(label+'.jsonl.partial');summary=out/'snapshots'/(label+'.json')
            cmd=[sys.executable,str(driver),'--root',str(root),'--toolchain',str(tool),'--artifacts',str(out/'probes'),'--census',str(a.census.resolve()),'--label',label,'--kind','probe']
            for src in sources:cmd+=['--probe-source',str(src)]
            cmd+=['--probe-output',str(raw),'--probe','/usr/bin/env','LEAN_PATH='+str(lib),str(tool/'bin/lean'),'-j1','-M12288','--tstack=131072','--run',str(helper),n,str(raw)]
            with (out/'driver.log').open('a') as log:r=subprocess.run(cmd,cwd=root,stdout=log,stderr=subprocess.STDOUT)
            if r.returncode:
                manifest.update(status='fail',failed_module=n,exit=r.returncode);save();raise ValueError('interface probe failed: '+n)
            result=interfaces.seal(raw,out/'probes'/label/'probe-result.json',n,summary)
            if result['schema']!=3:raise ValueError('unexpected snapshot schema')
            manifest['modules'].append(dict(module=n,summary=str(summary),summary_sha256=digest(summary),declarations=len(result['declarations']),raw_sha256=result['raw_sha256'],compressed_sha256=result['compressed_sha256']))
            save();print(f'{i+1}/{len(mods)} {n}',flush=True)
        manifest['status']='pass';save()
    finally:
        if manifest['status']=='running':
            manifest.update(status='fail',error='export interrupted or incomplete')
        save()

if __name__=='__main__':
    p=argparse.ArgumentParser()
    for k in ['root','toolchain','lib','artifacts','census']:p.add_argument('--'+k,type=pathlib.Path,required=True)
    p.add_argument('--label',required=True)
    export_all(p.parse_args())
