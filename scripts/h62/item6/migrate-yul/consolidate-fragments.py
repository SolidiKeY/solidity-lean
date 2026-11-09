#!/usr/bin/env python3
"""Verify complete old persisted-kernel inventory from complete explicitly versioned fragments.
This accepts old snapshot integrity only, never new-toolchain compatibility.
"""
import argparse,gzip,hashlib,json,pathlib,shutil,subprocess,sys,tempfile
sys.dont_write_bytecode=True
import interfaces
p=argparse.ArgumentParser()
for name in ['census','plan','source-view','output']:p.add_argument('--'+name,type=pathlib.Path,required=True)
p.add_argument('--prefix-only',action='store_true',help='verify available prefix only; result remains partial')
a=p.parse_args()
def sha(path):
    h=hashlib.sha256()
    with pathlib.Path(path).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
plan=json.loads(a.plan.read_text());census=json.loads(a.census.read_text())
assert not a.output.exists(), 'output must be fresh'
assert plan['schema_version']==2 and sha(a.census)==plan['original_census_sha256']
original=census['yul_modules']
assert original==plan['full_module_order'] and len(original)==plan['full_count']==census['yul_count']
assert [n for f in plan['fragments'] for n in f['expected_modules']]==original
records=[];configs=[];parent_hashes=[];cursor=0;complete=True
for fragment in plan['fragments']:
    expected=fragment['expected_modules']
    assert fragment['start']==cursor and fragment['end']==cursor+len(expected)
    cursor+=len(expected)
    assert fragment['schema'] in [2,3]
    assert fragment['helper_name']==('ExportInterfacesDag.lean' if fragment['schema']==3 else 'ExportInterfaces.lean')
    selected=json.loads(pathlib.Path(fragment['census']).read_text())
    assert sha(fragment['census'])==fragment['census_sha256']
    for key in ['modules','build_order','keysort_order']:assert selected[key]==census[key]
    path=pathlib.Path(fragment['manifest'])
    if not path.exists():
        assert a.prefix_only, 'fragment not available'
        complete=False;break
    parent=json.loads(path.read_text())
    if not fragment['allow_sealed_prefix'] and parent['status']!='pass':
        assert a.prefix_only, 'fragment incomplete'
        complete=False;break
    assert fragment['manifest_sha256'] is not None and sha(path)==fragment['manifest_sha256'], 'parent hash missing/drift'
    assert parent['census_sha256']==fragment['census_sha256']
    rows=parent['modules'];names=[r['module'] for r in rows]
    assert names==expected
    if fragment['mode']=='export':
        assert parent['module_count']==selected['yul_count']
        if fragment['allow_sealed_prefix']:assert names==selected['yul_modules'][:len(names)]
        else:assert names==selected['yul_modules']
    else:
        assert fragment['mode']=='single-probe' and len(rows)==parent['module_count']==1
        assert names[0] in selected['yul_modules']
    records.extend(rows);configs.extend([fragment]*len(rows));parent_hashes.append(sha(path))
assert [r['module'] for r in records]==original[:len(records)]
assert len(set(r['module'] for r in records))==len(records)
if complete:assert len(records)==len(original)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=a.source_view,text=True).strip()==base
for row in census['modules'].values():assert sha(a.source_view/row['path'])==row['sha256'], row['path']
report=dict(schema_version=2,status='running',scope='pinned old persisted-kernel inventory integrity only',base=base,source_view=str(a.source_view.resolve()),original_census_sha256=sha(a.census),parent_manifest_sha256=parent_hashes,plan_sha256=sha(a.plan),module_count=len(original),selected_for_verification=len(records),modules=[],migration_acceptance=False)
a.output.parent.mkdir(parents=True,exist_ok=True)
def save():a.output.write_text(json.dumps(report,indent=2)+'\n')
save()
try:
    version=None
    with tempfile.TemporaryDirectory(dir=a.output.parent,prefix='verify-old-') as tmp:
        rawpath=pathlib.Path(tmp)/'snapshot.jsonl'
        for index,row in enumerate(records):
            module=row['module'];path=pathlib.Path(row['summary'])
            assert sha(path)==row['summary_sha256'], module
            s=json.loads(path.read_text())
            assert s['module']==module and s['raw_sha256']==row['raw_sha256']
            assert sha(s['compressed'])==s['compressed_sha256']==row['compressed_sha256']
            with gzip.open(s['compressed'],'rb') as src,rawpath.open('wb') as dst:shutil.copyfileobj(src,dst)
            assert sha(rawpath)==s['raw_sha256']
            inspected=interfaces.inspect_snapshot(rawpath,module)
            for key in ['schema','module','header','footer','declarations']:assert inspected[key]==s[key], (module,key)
            assert len(s['declarations'])==row['declarations']
            assert sha(s['probe'])==s['probe_sha256']
            probe=interfaces.validate_probe(s['probe'])
            fragment=configs[index]
            assert s['schema']==fragment['schema']
            assert probe['census_sha256']==fragment['census_sha256']
            assert len(probe['modules'])==1 and len(probe['probe_outputs_after'])==1
            assert probe['probe_output_freshness_required'] is True
            cmd=probe['modules'][0]['command'];pos=cmd.index('--run')
            assert len(cmd)==pos+4 and cmd[pos+2]==module
            repository=pathlib.Path(probe['repository'])
            helper=pathlib.Path(cmd[pos+1]).resolve()
            assert helper==(repository/'tests/h62/item6/migrate-yul'/fragment['helper_name']).resolve()
            assert str(helper) in probe['probe_sources_before']
            assert sha(helper)==fragment['helper_sha256']==sha(a.source_view/'tests/h62/item6/migrate-yul'/fragment['helper_name'])
            output=pathlib.Path(cmd[pos+3]);output=(repository/output).resolve() if not output.is_absolute() else output.resolve()
            bound=probe['probe_outputs_after'];assert set(bound)=={str(output)}
            assert bound[str(output)]['sha256']==s['raw_sha256'] and bound[str(output)]['bytes']==rawpath.stat().st_size
            versions=(probe['lean'],probe['lake'])
            assert versions==(s['lean'],s['lake']) and 'version 4.24.0,' in probe['lean'] and '797c613eb9b6d4ec95db23e3e00af9ac6657f24b' in probe['lean']
            if version is None:version=versions
            assert versions==version
            assert probe['driver_sha256']==sha(a.source_view/'scripts/h62/item6/migrate-yul/build.py')
            assert probe['resource_helper_sha256']==sha(a.source_view/'scripts/h62/item6/migrate-yul/resources.py')
            report['modules'].append(dict(module=module,schema=s['schema'],summary=str(path),summary_sha256=sha(path),declarations=len(s['declarations']),public_declarations=sum(not d['private'] for d in s['declarations']),raw_sha256=s['raw_sha256'],compressed_sha256=s['compressed_sha256']))
            save()
            if (index+1)%100==0:print(f'{index+1}/{len(records)} verified',flush=True)
    report.update(status='pass' if complete else 'partial',lean=version[0],lake=version[1],declaration_records=sum(r['declarations'] for r in report['modules']),public_declaration_records=sum(r['public_declarations'] for r in report['modules']),limitation='All persisted old public/private/generated declarations retained. Not cross-version API equivalence, attribute/priority validation, new build, timing disposition or runtime acceptance.')
    save();print(('complete' if complete else 'available prefix')+' pinned old inventory integrity verified',flush=True)
finally:
    if report['status']=='running':report.update(status='fail',error='verification interrupted or incomplete');save()
