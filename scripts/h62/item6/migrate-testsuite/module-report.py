#!/usr/bin/env python3
"""Report every requested module without stopping on growth.
Full-build acceptance is separate. Failed/missing modules are never timing passes.
"""
import argparse,hashlib,json,math,re
from pathlib import Path

def provenance(old,new):
    errors=[]
    for k in ('settings','resources','parent_resources','runtime_image','cpu_affinity'):
        if k not in old or k not in new or old[k] is None or old[k]!=new[k]: errors.append('UNMATCHED_'+k)
    if not old.get('source_hashes') or old.get('source_hashes')!=new.get('source_hashes'): errors.append('UNMATCHED_DEPENDENCY_CLOSURE')
    configs=[]
    for label,s,version,commit in (('old',old,'4.24.0','797c613eb9b6d4ec95db23e3e00af9ac6657f24b'),('new',new,'4.35.0','eb6cafb7290e8bd5f2937522d8d804f58f02bafc')):
        v=s.get('versions',{})
        if f'version {version},' not in v.get('lean','') or commit not in v.get('lean','') or f'Lean version {version}' not in v.get('lake',''): errors.append('UNEXPECTED_TOOLCHAIN_'+label)
        try:
            data=Path(s['results'][0]['command'][2]).read_bytes()
            if hashlib.sha256(data).hexdigest()!=s.get('config_sha256'): errors.append('CONFIG_DIGEST_MISMATCH_'+label)
            configs.append(re.sub(r'(?m)^buildDir = .*$', 'buildDir = "PRIVATE"',data.decode()))
        except (OSError,KeyError,IndexError,UnicodeError): errors.append('MISSING_CONFIG_'+label)
    if len(configs)==2 and configs[0]!=configs[1]: errors.append('UNMATCHED_CONFIG')
    return errors

def report(old,new,census):
    rows=[];left={r['module']:r for r in old['results']};right={r['module']:r for r in new['results']}
    for s,mapped in ((old,left),(new,right)):
        if len(set(s['requested_modules']))!=len(s['requested_modules']): raise ValueError('DUPLICATE_REQUEST')
        if len(mapped)!=len(s['results']): raise ValueError('DUPLICATE_MODULE_RECORD')
        if set(mapped)-set(s['requested_modules']): raise ValueError('UNREQUESTED_MODULE_RECORD')
    errors=provenance(old,new);same_requested=old['requested_modules']==new['requested_modules']
    full_scope=old.get('full_assigned_build') is True and new.get('full_assigned_build') is True
    for name in dict.fromkeys(old['requested_modules']+new['requested_modules']):
        if name not in census['module_paths']: raise ValueError('MISSING_CENSUS_MODULE: '+name)
        a=left.get(name);b=right.get(name);path=census['module_paths'][name]
        same_source=path in old['source_hashes'] and path in new['source_hashes'] and old['source_hashes'][path]==new['source_hashes'][path]
        row={'module':name,'owned':name in census['owned'],'old':a,'new':b,'source_matches':same_source}
        eligible=not errors and same_requested and full_scope and same_source and all(r is not None and r['exit']==0 and r['stop'] is None for r in (a,b))
        row['comparable_successful_measurements']=eligible
        if eligible:
            values=[r[k] for r in (a,b) for k in ('wall_s','sampled_aggregate_peak_rss_bytes')]
            if any(not isinstance(v,(int,float)) or not math.isfinite(v) or v<=0 for v in values): raise ValueError('INVALID_METRIC')
            row.update(wall_delta_percent=(b['wall_s']/a['wall_s']-1)*100,sampled_peak_rss_delta_percent=(b['sampled_aggregate_peak_rss_bytes']/a['sampled_aggregate_peak_rss_bytes']-1)*100)
        rows.append(row)
    return {'kind':'per-module report only; growth does not stop lane; no full-build acceptance claim','provenance_errors':errors,'requested_modules_match':same_requested,'versions':{'old':old.get('versions'),'new':new.get('versions')},'old_status':old['status'],'new_status':new['status'],'rows':rows}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('old',type=Path);p.add_argument('new',type=Path);p.add_argument('census',type=Path);a=p.parse_args()
    print(json.dumps(report(json.loads(a.old.read_text()),json.loads(a.new.read_text()),json.loads(a.census.read_text())),sort_keys=True,indent=2,allow_nan=False))
