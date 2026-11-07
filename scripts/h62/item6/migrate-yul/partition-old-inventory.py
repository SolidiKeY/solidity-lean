#!/usr/bin/env python3
"""Preserve a verified old inventory prefix and plan every remaining module.
A failed/interrupted export supplies complete sealed prefixes only, never a pass.
"""
import argparse,gzip,hashlib,json,pathlib,sys
sys.dont_write_bytecode=True
import interfaces
p=argparse.ArgumentParser()
p.add_argument('--census',type=pathlib.Path,required=True)
p.add_argument('--prefix-manifest',type=pathlib.Path,required=True)
p.add_argument('--out',type=pathlib.Path,required=True)
a=p.parse_args()
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
c=json.loads(a.census.read_text());prefix=json.loads(a.prefix_manifest.read_text())
assert prefix['census_sha256']==sha(a.census), 'prefix is from a different source census'
full=c['yul_modules'];assert len(full)==len(set(full))==c['yul_count']
rows=prefix['modules'];names=[r['module'] for r in rows]
assert names==full[:len(names)], 'prefix order/coverage differs'
assert len(names)<len(full), 'no remaining inventory'
for row in rows:
    path=pathlib.Path(row['summary']);assert sha(path)==row['summary_sha256']
    s=json.loads(path.read_text());assert s['module']==row['module']
    assert s['raw_sha256']==row['raw_sha256']
    assert sha(s['compressed'])==s['compressed_sha256']==row['compressed_sha256']
    with gzip.open(s['compressed'],'rb') as f:raw=f.read()
    assert hashlib.sha256(raw).hexdigest()==row['raw_sha256']
    assert s['schema']==2 and s['header']['import_level']=='private' and s['header']['import_all'] is True
    parsed=[json.loads(line) for line in raw.decode().splitlines()]
    assert parsed[0]==s['header'] and parsed[-1]==s['footer']
    assert len(parsed)-2==len(s['declarations'])
    assert all(d.get('record')=='declaration' and d['module']==interfaces.module_name(row['module']) for d in parsed[1:-1])
    assert len({interfaces.canonical(d['name']) for d in parsed[1:-1]})==len(s['declarations'])
    assert sha(s['probe'])==s['probe_sha256']
    probe=interfaces.validate_probe(s['probe'])
    assert probe['lean']==s['lean'] and probe['lake']==s['lake']
    assert 'version 4.24.0,' in probe['lean']
    assert probe['driver_sha256']==sha(pathlib.Path(__file__).with_name('build.py'))
    assert probe['resource_helper_sha256']==sha(pathlib.Path(__file__).with_name('resources.py'))
    assert len(probe['modules'])==1 and len(probe['probe_outputs_after'])==1
    assert next(iter(probe['probe_outputs_after'].values()))['sha256']==row['raw_sha256']
    assert s['footer']['count']==len(s['declarations'])==row['declarations']
    assert probe['census_sha256']==sha(a.census)
remaining=full[len(names):]
assert set(names).isdisjoint(remaining) and names+remaining==full
out=a.out.resolve();out.mkdir(parents=True,exist_ok=False)
subset=dict(c,yul_modules=remaining,yul_count=len(remaining))
(out/'remaining-census.json').write_text(json.dumps(subset,indent=2,sort_keys=True)+'\n')
plan=dict(schema_version=1,status='partial',full_count=len(full),sealed_prefix_count=len(names),remaining_count=len(remaining),full_module_order=full,prefix_manifest=str(a.prefix_manifest.resolve()),prefix_manifest_sha256=sha(a.prefix_manifest),original_census=str(a.census.resolve()),original_census_sha256=sha(a.census),remaining_census=str(out/'remaining-census.json'),remaining_census_sha256=sha(out/'remaining-census.json'),prefix_records=rows,limitation='Prefix+remaining are exact coverage partitions, not exclusions. New export and final consolidation remain pending; no API/migration acceptance.')
(out/'coverage-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps(dict(status='prefix_integrity_pass',sealed=len(names),remaining=len(remaining),total=len(full),migration_acceptance=False)))
