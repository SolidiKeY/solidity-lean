#!/usr/bin/env python3
"""Bounded serial interface snapshots. Bulk payloads stay outside Git.
Structural agreement is not semantic equivalence, proof replay or budget validation.
"""
import argparse,gzip,hashlib,json,os,pathlib,re,shutil,subprocess,sys
sys.dont_write_bytecode=True
import importlib.util
_dag_spec=importlib.util.spec_from_file_location("h62_expr_dag",pathlib.Path(__file__).with_name("expr_dag.py"))
expr_dag=importlib.util.module_from_spec(_dag_spec);_dag_spec.loader.exec_module(expr_dag)

def digest(path):
    h=hashlib.sha256()
    with pathlib.Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()

def canonical(x):return json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':'))
def fingerprint(x):return hashlib.sha256(canonical(x).encode()).hexdigest()
def expr_hash(text):
    if not isinstance(text,str) or not text.startswith('['):raise ValueError('missing structural expression text')
    return hashlib.sha256(text.encode()).hexdigest()

def module_name(text):
    n=['anonymous']
    for part in text.split('.'):
        if not part:raise ValueError('empty module component')
        n=['str',n,part]
    return n

def validate_probe(path):
    p=json.loads(pathlib.Path(path).read_text())
    if p['status']!='pass' or p['kind']!='probe' or not p['modules']:raise ValueError('probe did not complete')
    if any(m['exit']!=0 or m.get('stop') for m in p['modules']):raise ValueError('probe command failed')
    before=p['probe_sources_before'];after=p['probe_sources_after']
    if not before or before!=after:raise ValueError('probe source binding missing/mismatched')
    for name,expected in before.items():
        if digest(name)!=expected:raise ValueError('probe source differs: '+name)
    for key in ['source_check_before','source_check_after']:
        if p[key]['status']!='pass':raise ValueError('census source check failed')
    return p

def inspect_snapshot(raw,expected_module):
    header=None;footer=None;rows=[];seen=set()
    wanted=module_name(expected_module)
    with pathlib.Path(raw).open() as f:
        for line in f:
            row=json.loads(line)
            kind=row.get('record')
            if footer is not None:raise ValueError('data after completion footer')
            if header is None:
                if kind!='header' or (type(row.get('schema')) is not int or row['schema'] not in [2,3]):raise ValueError('missing/unsupported snapshot header')
                if row.get('module')!=wanted or row.get('import_level')!='private' or row.get('import_all') is not True:raise ValueError('module/import mode mismatch')
                if row['extra_codegen_count']!=len(row['extra_codegen_names']):raise ValueError('IR coverage mismatch')
                if row['schema']==3 and row.get('expression_encoding')!='canonical expr-dag-v1 JSON text, metadata erased only':raise ValueError('unknown DAG expression encoding')
                header=row;continue
            if row.get('module')!=wanted:raise ValueError('record module mismatch')
            if kind=='complete':footer=row;continue
            if kind!='declaration':raise ValueError('unknown snapshot record')
            name=canonical(row['name'])
            if name in seen:raise ValueError('duplicate kernel declaration')
            seen.add(name)
            if header['schema']==3:
                expr_dag.loads(row['type'])
                for field in ['implementation','proof']:
                    if field in row['payload']:expr_dag.loads(row['payload'][field])
                for rule in row['payload'].get('rules',[]):expr_dag.loads(rule['rhs'])
            signature={k:row[k] for k in ['name','kind','universes','unsafe','partial','type']}
            meta=dict(row['payload']);impl=meta.pop('implementation',None);proof=meta.pop('proof',None)
            rows.append(dict(name=row['name'],display_name=row['display_name'],kind=row['kind'],private=row['private'],shared=row['shared'],authoritative_origin=row['authoritative_origin'],type_sha256=expr_hash(row['type']),signature_sha256=fingerprint(signature),implementation_sha256=expr_hash(impl) if impl is not None else None,proof_sha256=expr_hash(proof) if proof is not None else None,declaration_metadata_sha256=fingerprint(meta)))
    if header is None or footer is None:raise ValueError('incomplete snapshot')
    if footer['count']!=len(rows) or header['expected_constants']!=len(rows):raise ValueError('declaration coverage/count mismatch')
    if len({canonical(n) for n in footer['axiom_union']})!=len(footer['axiom_union']):raise ValueError('duplicate axiom record')
    return dict(schema=header['schema'],module=expected_module,header=header,footer=footer,declarations=rows)

def seal(raw,probe_path,expected_module,output):
    raw=pathlib.Path(raw);output=pathlib.Path(output)
    if output.exists():raise ValueError('refusing existing sealed summary')
    probe=validate_probe(probe_path)
    if probe.get('probe_output_freshness_required') is not True:raise ValueError('output freshness not enforced')
    bound=probe.get('probe_outputs_after',{}).get(str(raw.resolve()))
    if not bound or bound['sha256']!=digest(raw) or bound['bytes']!=raw.stat().st_size:raise ValueError('snapshot output not bound to probe')
    if len(probe['modules'])!=1:raise ValueError('expected one exporter command')
    cmd=probe['modules'][0]['command']
    try:idx=cmd.index('--run')
    except ValueError:raise ValueError('not an exporter command')
    if len(cmd)!=idx+4 or cmd[idx+2]!=expected_module:raise ValueError('exporter/module arguments mismatch')
    repo=pathlib.Path(probe['repository'])
    helper=(repo/cmd[idx+1]).resolve()
    with raw.open() as stream:
        try: first=json.loads(next(stream))
        except (StopIteration,json.JSONDecodeError) as err:raise ValueError('missing/invalid snapshot header') from err
    if not isinstance(first,dict) or type(first.get('schema')) is not int or first['schema'] not in [2,3]:raise ValueError('unknown snapshot schema')
    helper_name='ExportInterfacesDag.lean' if first['schema']==3 else 'ExportInterfaces.lean'
    expected_helper=(repo/'tests/h62/item6/migrate-yul'/helper_name).resolve()
    requested=(repo/cmd[idx+3]).resolve()
    if helper!=expected_helper or str(helper) not in probe['probe_sources_before'] or requested!=raw.resolve():raise ValueError('exporter/output argument binding mismatch')
    result=inspect_snapshot(raw,expected_module)
    result.update(raw_sha256=digest(raw),probe_sha256=digest(probe_path),probe=str(pathlib.Path(probe_path).resolve()),lean=probe['lean'],lake=probe['lake'],bound_sources=probe['probe_sources_before'])
    compressed=output.with_suffix('.jsonl.gz');partial=compressed.with_suffix('.gz.partial')
    if compressed.exists() or partial.exists():raise ValueError('refusing existing compressed snapshot')
    with partial.open('wb') as dest:
        with gzip.GzipFile(filename='',mode='wb',fileobj=dest,mtime=0) as z,raw.open('rb') as src:shutil.copyfileobj(src,z)
    h=hashlib.sha256()
    with gzip.open(partial,'rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    if h.hexdigest()!=result['raw_sha256']:raise ValueError('compressed snapshot verification failed')
    os.replace(partial,compressed)
    result.update(compressed=str(compressed.resolve()),compressed_sha256=digest(compressed))
    output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    # Retain the verified compressed raw snapshot; remove only our .partial.
    if raw.name.endswith('.partial'):raw.unlink()
    return result

def compare_snapshots(old,new):
    if old['schema'] not in [2,3] or old['schema']!=new['schema'] or old['module']!=new['module']:raise ValueError('incomparable snapshot scope/schema')
    a={canonical(r['name']):r for r in old['declarations']};b={canonical(r['name']):r for r in new['declarations']}
    fields=['type_sha256','signature_sha256','implementation_sha256','proof_sha256','declaration_metadata_sha256']
    changes={field:[dict(name=a[n]['name'],display_name=a[n]['display_name'],old=a[n][field],new=b[n][field]) for n in sorted(a.keys() & b.keys()) if a[n][field]!=b[n][field]] for field in fields}
    provenance_fields=['display_name','private','shared','authoritative_origin']
    changes['provenance']=[dict(name=a[n]['name'],old={k:a[n][k] for k in provenance_fields},new={k:b[n][k] for k in provenance_fields}) for n in sorted(a.keys() & b.keys()) if any(a[n][k]!=b[n][k] for k in provenance_fields)]
    header_changes={k:dict(old=old['header'].get(k),new=new['header'].get(k)) for k in sorted(old['header'].keys() | new['header'].keys()) if old['header'].get(k)!=new['header'].get(k)}
    missing=[a[n]['name'] for n in sorted(a.keys()-b.keys())];added=[b[n]['name'] for n in sorted(b.keys()-a.keys())]
    axiom_change=old['footer']['axiom_union']!=new['footer']['axiom_union']
    any_change=bool(missing or added or axiom_change or header_changes or any(changes.values()))
    return dict(status='differences_require_review' if any_change else 'structural_agreement_only',limitation='No semantic equivalence, proof replay, attribute compatibility or build-budget acceptance is implied.',module=old['module'],missing=missing,added=added,changes=changes,header_changes=header_changes,old_axioms=old['footer']['axiom_union'],new_axioms=new['footer']['axiom_union'])

def export_all(a):
    root=a.root.resolve();out=a.artifacts.resolve()/a.label
    if not re.fullmatch(r'[A-Za-z0-9_-]+',a.label):raise ValueError('invalid label')
    out.mkdir(parents=True,exist_ok=False);(out/'snapshots').mkdir()
    census=json.loads(a.census.read_text());mods=census['yul_modules']
    helper=root/'tests/h62/item6/migrate-yul/ExportInterfaces.lean'
    driver=root/'scripts/h62/item6/migrate-yul/build.py'
    tool=a.toolchain.resolve();lib=a.lib.resolve()
    manifest=dict(status='running',scope='persisted kernel declarations; source cases require prescribed builds',module_count=len(mods),census_sha256=digest(a.census),helper_sha256=digest(helper),wrapper_sha256=digest(__file__),modules=[])
    path=out/'manifest.json'
    def save():path.write_text(json.dumps(manifest,indent=2)+'\n')
    missing=[n for n in mods if not (lib/(n.replace('.','/')+'.olean')).is_file()]
    if missing:
        manifest.update(status='blocked',blocker='MISSING_BUILT_MODULES',missing=missing);save();raise ValueError('full interface export lacks '+str(len(missing))+' built modules')
    save()
    try:
        for i,n in enumerate(mods):
            if digest(helper)!=manifest['helper_sha256'] or digest(a.census)!=manifest['census_sha256']:raise ValueError('export inputs changed')
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
            result=seal(raw,out/'probes'/label/'probe-result.json',n,summary)
            manifest['modules'].append(dict(module=n,summary=str(summary),summary_sha256=digest(summary),declarations=len(result['declarations']),raw_sha256=result['raw_sha256'],compressed_sha256=result['compressed_sha256']))
            save();print(f'{i+1}/{len(mods)} {n}',flush=True)
        manifest['status']='pass';save()
    finally:
        if manifest['status']=='running':
            manifest.update(status='fail',error='export interrupted or incomplete')
        save()

if __name__=='__main__':
    p=argparse.ArgumentParser();sub=p.add_subparsers(dest='mode',required=True)
    q=sub.add_parser('seal');q.add_argument('raw',type=pathlib.Path);q.add_argument('probe',type=pathlib.Path);q.add_argument('module');q.add_argument('output',type=pathlib.Path)
    q=sub.add_parser('compare');q.add_argument('old',type=pathlib.Path);q.add_argument('new',type=pathlib.Path);q.add_argument('output',type=pathlib.Path)
    q=sub.add_parser('export');
    for k in ['root','toolchain','lib','artifacts','census']:q.add_argument('--'+k,type=pathlib.Path,required=True)
    q.add_argument('--label',required=True)
    a=p.parse_args()
    try:
        if a.mode=='seal':seal(a.raw,a.probe,a.module,a.output);print('snapshot sealed: '+str(a.output))
        elif a.mode=='compare':
            result=compare_snapshots(json.loads(a.old.read_text()),json.loads(a.new.read_text()))
            a.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n');print(result['status'])
            if result['status']=='differences_require_review':sys.exit(2)
        else:export_all(a)
    except (ValueError,KeyError,OSError) as e:print(str(e),file=sys.stderr);sys.exit(1)
