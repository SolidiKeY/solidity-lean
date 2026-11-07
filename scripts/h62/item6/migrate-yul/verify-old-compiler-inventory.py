#!/usr/bin/env python3
"""Read back complete old compiler observations and all supervised byte bindings.
Integrity of old observations does not establish public/API or semantic compatibility.
"""
import argparse,gzip,hashlib,importlib.util,json,pathlib,sys
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('compiler_batches',pathlib.Path(__file__).with_name('compiler-signatures-batch.py'))
batch=importlib.util.module_from_spec(spec);spec.loader.exec_module(batch)
digest=batch.interfaces.digest
ORIGINAL_CENSUS_SHA256="fac7f44fac55ba732eeb9b6151a0f001ddc4dd6d0cf10558642ffd1c30b22902"

def verify(manifest_path,census_path,name_census_path):
    manifest_path=pathlib.Path(manifest_path);census_path=pathlib.Path(census_path);name_census_path=pathlib.Path(name_census_path)
    manifest=json.loads(manifest_path.read_text());census=json.loads(census_path.read_text());names=json.loads(name_census_path.read_text())
    if manifest['status']!='pass' or manifest['base']!='c6f550e281a7e5affa9a99bc2cdaed556dec00e4' or manifest['migration_acceptance'] is not False or manifest['one_module_per_probe'] is not True:
        raise ValueError('requires completed pinned old-only inventory')
    if digest(census_path)!=ORIGINAL_CENSUS_SHA256:
        raise ValueError('requires exact original pinned census')
    if manifest['census_sha256']!=digest(census_path) or manifest['name_census_sha256']!=digest(name_census_path):
        raise ValueError('census binding mismatch')
    if names['status']!='pass' or names['base']!=manifest['base'] or names['migration_acceptance'] is not False:
        raise ValueError('invalid source name census')
    if digest(names['inventory'])!=names['inventory_sha256']:
        raise ValueError('old kernel inventory binding mismatch')
    kernel=json.loads(pathlib.Path(names['inventory']).read_text())
    if kernel['status']!='pass' or kernel['base']!=manifest['base'] or kernel['migration_acceptance'] is not False or kernel['original_census_sha256']!=digest(census_path):
        raise ValueError('old kernel provenance mismatch')
    modules=census['yul_modules'];rows=manifest['modules']
    if len(modules)!=1774:raise ValueError('original corpus size mismatch')
    if len(set(modules))!=len(modules) or [r['module'] for r in rows]!=modules or [r['module'] for r in names['modules']]!=modules or [r['module'] for r in kernel['modules']]!=modules:
        raise ValueError('ordered full module coverage mismatch')
    for value in [manifest['module_count'],names['module_count'],kernel['module_count'],kernel['selected_for_verification']]:
        if type(value) is not int or value!=len(modules):raise ValueError('module count mismatch')
    original_input_hashes=dict(manifest['input_sources']);original_manifest_hash=digest(manifest_path)
    for path,sha in original_input_hashes.items():
        if digest(path)!=sha:raise ValueError('bound input drift')
    found=missing=total=empty=queried=0;all_names=set();reports=[];version=None
    for i,(row,expected,origin) in enumerate(zip(rows,names['modules'],kernel['modules'])):
        if expected['summary']!=origin['summary'] or expected['summary_sha256']!=origin['summary_sha256'] or digest(origin['summary'])!=origin['summary_sha256']:
            raise ValueError('original summary identity/digest mismatch')
        source=json.loads(pathlib.Path(origin['summary']).read_text());header=source['header'];wanted=header['extra_codegen_names']
        count=header['extra_codegen_count']
        if source['module']!=row['module'] or wanted!=expected['extra_codegen_names'] or type(count) is not int or count!=len(wanted) or type(expected['compiler_name_records']) is not int or count!=expected['compiler_name_records']:
            raise ValueError('original name coverage/count mismatch')
        if type(row['name_count']) is not int or count!=row['name_count']:raise ValueError('manifest name count mismatch')
        for name in wanted:
            batch.interfaces.expr_dag.name(name)
            encoded=batch.interfaces.canonical(name)
            if encoded in all_names:raise ValueError('duplicate original compiler name')
            all_names.add(encoded)
        total+=count
        if count==0:
            if row!=dict(module=row['module'],mode='empty_from_verified_old_kernel_header',name_count=0,summary=origin['summary'],summary_sha256=origin['summary_sha256'],ir_query_performed=False):
                raise ValueError('empty header falsely claims a query')
            empty+=1;continue
        if row['mode']!='supervised_old_IR_query':raise ValueError('nonempty module lacks supervised query')
        summary_path=pathlib.Path(row['summary'])
        if digest(summary_path)!=row['summary_sha256']:raise ValueError('sealed summary drift')
        summary=json.loads(summary_path.read_text())
        sealed=batch.seal(row['probe'],summary['jobs'])
        if len(sealed)!=1 or sealed[0]['module']!=row['module']:raise ValueError('not a one-module query')
        recomputed=sealed[0]
        recomputed.update(compressed=summary['compressed'],compressed_sha256=summary['compressed_sha256'],original_summary=origin['summary'],original_summary_sha256=origin['summary_sha256'])
        if recomputed!=summary:raise ValueError('sealed report differs from raw/probe validation')
        if [r['name'] for r in summary['declarations']]!=wanted:raise ValueError('queried original names/order differ')
        if row['probe_sha256']!=summary['probe_sha256'] or row['raw_sha256']!=summary['raw_sha256'] or row['compressed']!=summary['compressed'] or row['compressed_sha256']!=summary['compressed_sha256']:
            raise ValueError('manifest summary/probe/raw/gzip bindings differ')
        if digest(summary['compressed'])!=summary['compressed_sha256']:raise ValueError('compressed bytes differ')
        raw_hash=hashlib.sha256()
        with gzip.open(summary['compressed'],'rb') as src:
            for block in iter(lambda:src.read(1024*1024),b''):raw_hash.update(block)
        if raw_hash.hexdigest()!=summary['raw_sha256']:raise ValueError('gzip does not reproduce raw bytes')
        if row['ir_found']!=summary['footer']['ir_found'] or row['ir_missing']!=summary['footer']['ir_missing']:raise ValueError('IR lookup count mismatch')
        versions=(summary['lean'],summary['lake'])
        if 'version 4.24.0,' not in versions[0] or '797c613eb9b6d4ec95db23e3e00af9ac6657f24b' not in versions[0]:raise ValueError('wrong toolchain')
        if version is None:version=versions
        if versions!=version:raise ValueError('mixed toolchains')
        found+=row['ir_found'];missing+=row['ir_missing'];queried+=1
        reports.append(dict(module=row['module'],summary=str(summary_path),sha256=row['summary_sha256']))
        if (i+1)%100==0:print(f'{i+1}/{len(modules)} old compiler modules verified',flush=True)
    for field,value in [('compiler_name_records',total),('ir_found',found),('ir_missing',missing)]:
        if type(manifest[field]) is not int or manifest[field]!=value:raise ValueError('final total mismatch')
    if total!=32734:raise ValueError('original extra-name total mismatch')
    if found+missing!=total or names['compiler_name_records']!=total or names['unique_compiler_names']!=len(all_names):raise ValueError('original global name total mismatch')
    if digest(manifest_path)!=original_manifest_hash:raise ValueError('manifest changed while checking')
    for path,sha in original_input_hashes.items():
        if digest(path)!=sha:raise ValueError('bound input changed while checking')
    return dict(schema_version=1,status='pass',scope='complete pinned old compiler observation integrity only',base=manifest['base'],manifest=str(manifest_path.resolve()),manifest_sha256=original_manifest_hash,census_sha256=digest(census_path),name_census_sha256=digest(name_census_path),module_count=len(modules),supervised_modules=queried,derived_empty_modules=empty,compiler_name_records=total,unique_compiler_names=len(all_names),ir_found=found,ir_missing=missing,lean=version[0],lake=version[1],verified_reports=reports,verifier_sha256=digest(__file__),migration_acceptance=False,implemented_shims=[],limitation='Missing IR and public visibility remain unresolved; terminal IR Repr text is not typechecked by this validator. Not attribute validation, new-toolchain compatibility, semantic proof or performance acceptance.')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['manifest','census','name-census','output']:p.add_argument('--'+key,type=pathlib.Path,required=True)
    a=p.parse_args()
    if a.output.exists():raise SystemExit('output must be fresh')
    result=verify(a.manifest,a.census,a.name_census)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print('complete old compiler observations verified',flush=True)
