#!/usr/bin/env python3
"""Complete original old extra-name inventory using measured one-module jobs.
Never runs v4.35, waives a name, or accepts public/API/semantic compatibility.
"""
import sys
sys.dont_write_bytecode=True
import argparse,contextlib,fcntl,gzip,importlib.util,json,os,pathlib,re,signal,subprocess
spec=importlib.util.spec_from_file_location('compiler_batches',pathlib.Path(__file__).with_name('compiler-signatures-batch.py'))
batch=importlib.util.module_from_spec(spec);spec.loader.exec_module(batch)
digest=batch.interfaces.digest
BASE='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
@contextlib.contextmanager
def writer():
    with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        yield

def validate_plan(census,names,kernel):
    selected=census['yul_modules'];expected=names['modules'];persisted=kernel['modules']
    if len(set(selected))!=len(selected) or [row['module'] for row in expected]!=selected or [row['module'] for row in persisted]!=selected:
        raise ValueError('original ordered module coverage mismatch')
    if names['module_count']!=len(selected) or kernel['module_count']!=len(selected) or kernel['selected_for_verification']!=len(selected):
        raise ValueError('original module count mismatch')
    total=0
    for row,origin in zip(expected,persisted):
        if row['summary']!=origin['summary'] or row['summary_sha256']!=origin['summary_sha256']:
            raise ValueError('summary not bound to kernel inventory')
        if digest(row['summary'])!=origin['summary_sha256']:
            raise ValueError('old summary drift: '+row['module'])
        snapshot=json.loads(pathlib.Path(row['summary']).read_text());header=snapshot['header']
        count=row['compiler_name_records'];header_count=header['extra_codegen_count']
        if type(count) is not int or type(header_count) is not int or count<0 or count!=header_count or count!=len(header['extra_codegen_names']):
            raise ValueError('name count contradicts verified header')
        if snapshot['module']!=row['module'] or header['extra_codegen_names']!=row['extra_codegen_names']:
            raise ValueError('old name provenance mismatch')
        total+=header_count
    if type(names['compiler_name_records']) is not int or total!=names['compiler_name_records']:
        raise ValueError('full compiler-name total mismatch')
    return expected

def export(a):
    root=a.root.resolve();tool=a.toolchain.resolve();lib=a.lib.resolve();out=a.artifacts.resolve()/a.label
    if not re.fullmatch(r'[A-Za-z0-9_-]+',a.label):raise ValueError('invalid label')
    if subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()!=BASE:raise ValueError('requires preserved original source view')
    version=subprocess.check_output([str(tool/'bin/lean'),'--version'],text=True).strip()
    if 'version 4.24.0,' not in version or '797c613eb9b6d4ec95db23e3e00af9ac6657f24b' not in version:raise ValueError('old4.24only; new-toolchain performanceSTOP remains')
    census=json.loads(a.census.read_text());names=json.loads(a.name_census.read_text())
    if names['status']!='pass' or names['base']!=BASE or names['migration_acceptance'] is not False:raise ValueError('invalid old name census')
    if digest(names['inventory'])!=names['inventory_sha256']:raise ValueError('old kernel inventory drift')
    kernel=json.loads(pathlib.Path(names['inventory']).read_text())
    if kernel['status']!='pass' or kernel['base']!=BASE or kernel['migration_acceptance'] is not False or kernel['original_census_sha256']!=digest(a.census):raise ValueError('old inventory/census provenance mismatch')
    selected=census['yul_modules'];expected=validate_plan(census,names,kernel)
    helper=root/'tests/h62/item6/migrate-yul/ExportCompilerSignaturesBatch.lean';driver=root/'scripts/h62/item6/migrate-yul/build.py'
    if digest(helper)!=digest(pathlib.Path(__file__).resolve().parents[4]/'tests/h62/item6/migrate-yul/ExportCompilerSignaturesBatch.lean'):raise ValueError('baseline helper copy differs')
    bound=[pathlib.Path(__file__),pathlib.Path(batch.__file__),pathlib.Path(batch.collector.__file__),pathlib.Path(batch.interfaces.__file__),pathlib.Path(batch.interfaces.expr_dag.__file__),helper,driver,driver.with_name('resources.py'),a.census,a.name_census,pathlib.Path(names['inventory'])]
    hashes={str(p.resolve()):digest(p) for p in bound}
    manifest=dict(schema_version=1,status='running',scope='original old extraConstNames IR observations; no publicAPI/semantic acceptance',base=BASE,lean=version,module_count=len(selected),name_census_sha256=digest(a.name_census),census_sha256=digest(a.census),input_sources=hashes,modules=[],migration_acceptance=False,one_module_per_probe=True)
    def unchanged():
        if any(digest(path)!=sha for path,sha in hashes.items()):raise ValueError('export inputs changed')
    def save():
        with writer():(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    with writer():out.mkdir(parents=True,exist_ok=False);(out/'snapshots').mkdir();(out/'jobs').mkdir()
    active=None
    def interrupted(signum,frame):
        if active is not None:
            active.terminate()
            active.wait(timeout=15)
        raise SystemExit(128+signum)
    for sig in [signal.SIGTERM,signal.SIGINT,signal.SIGHUP]:signal.signal(sig,interrupted)
    save()
    try:
        for i,row in enumerate(expected):
            unchanged();module=row['module'];count=row['compiler_name_records']
            if type(count) is not int or count<0:raise ValueError('invalid original name count')
            if count==0:
                manifest['modules'].append(dict(module=module,mode='empty_from_verified_old_kernel_header',name_count=0,summary=row['summary'],summary_sha256=row['summary_sha256'],ir_query_performed=False))
            else:
                label=f'module-{i:04d}';raw=out/'snapshots'/(label+'.jsonl');summary=out/'snapshots'/(label+'.json');jobs=out/'jobs'/(label+'.json')
                with writer():jobs.write_text(json.dumps([dict(module=module,output=str(raw))],indent=2)+'\n')
                olean=lib/(module.replace('.','/')+'.olean');sources=[olean]+[pathlib.Path(str(olean)+suffix) for suffix in ['.private','.server'] if pathlib.Path(str(olean)+suffix).exists()]
                if not olean.is_file():raise ValueError('missing built module: '+module)
                cmd=[sys.executable,str(driver),'--root',str(root),'--toolchain',str(tool),'--artifacts',str(out/'probes'),'--census',str(a.census.resolve()),'--label',label,'--kind','probe','--probe-source',str(helper),'--probe-source',str(jobs)]
                for source in sources:cmd+=['--probe-source',str(source)]
                cmd+=['--probe-output',str(raw),'--probe','/usr/bin/env','LEAN_PATH='+str(lib),str(tool/'bin/lean'),'-j1','-M12288','--tstack=131072','--run',str(helper),str(jobs)]
                with (out/'driver.log').open('a') as log:
                    active=subprocess.Popen(cmd,cwd=root,stdout=log,stderr=subprocess.STDOUT)
                    code=active.wait();active=None
                if code:raise ValueError('old compiler probe failed: '+module+' exit '+str(code))
                unchanged();sealed=batch.seal(out/'probes'/label/'probe-result.json',jobs)
                if len(sealed)!=1:raise ValueError('one-module sealing mismatch')
                report=sealed[0]
                if [d['name'] for d in report['declarations']]!=row['extra_codegen_names']:raise ValueError('original compiler-name order/coverage mismatch')
                compressed=raw.with_suffix('.jsonl.gz')
                with writer():
                    with compressed.open('xb') as dest:
                        with gzip.GzipFile(filename='',mode='wb',fileobj=dest,mtime=0) as z:z.write(raw.read_bytes())
                    report.update(compressed=str(compressed),compressed_sha256=digest(compressed),original_summary=row['summary'],original_summary_sha256=row['summary_sha256'])
                    summary.write_text(json.dumps(report,indent=2)+'\n')
                manifest['modules'].append(dict(module=module,mode='supervised_old_IR_query',name_count=count,ir_found=report['footer']['ir_found'],ir_missing=report['footer']['ir_missing'],summary=str(summary),summary_sha256=digest(summary),probe=report['probe'],probe_sha256=report['probe_sha256'],raw_sha256=report['raw_sha256'],compressed=str(compressed),compressed_sha256=digest(compressed)))
            save()
            if (i+1)%25==0 or i+1==len(expected):print(f'{i+1}/{len(expected)} original modules accounted',flush=True)
        unchanged();validate_plan(census,names,kernel)
        if subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()!=BASE:raise ValueError('original source view head changed')
        for source in census['modules'].values():
            if digest(root/source['path'])!=source['sha256']:raise ValueError('original source changed at completion')
        manifest.update(compiler_name_records=sum(row['name_count'] for row in manifest['modules']),ir_found=sum(row.get('ir_found',0) for row in manifest['modules']),ir_missing=sum(row.get('ir_missing',0) for row in manifest['modules']))
        if manifest['compiler_name_records']!=names['compiler_name_records']:raise ValueError('full name total mismatch')
        manifest['status']='pass';save()
    finally:
        if manifest['status']=='running':manifest.update(status='fail',error='export interrupted or incomplete; retain only sealed prefix');save()

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['root','toolchain','lib','artifacts','census','name-census']:p.add_argument('--'+key,type=pathlib.Path,required=True)
    p.add_argument('--label',required=True)
    export(p.parse_args())
