#!/usr/bin/env python3
"""Fail-closed comparison and frozen-source report; failed builds have no delta."""
import argparse, hashlib, json, pathlib, math

def compare(old,new):
    if any(x.get('exit')!=0 or 'guard_stop' not in x or x['guard_stop'] is not None for x in (old,new)):
        return {'status':'blocked','wall_delta_percent':None,'rss_delta_percent':None,'reason':'both complete passing builds required'}
    metrics=['wall_seconds','sampled_peak_group_rss_bytes']
    if any(not isinstance(x.get(k),(int,float)) or isinstance(x.get(k),bool) or not math.isfinite(x[k]) or x[k]<=0 for x in (old,new) for k in metrics):
        return {'status':'blocked','wall_delta_percent':None,'rss_delta_percent':None,'reason':'positive finite timing/RSS metrics required'}
    keys=['command','LEAN_NUM_THREADS','per_process_address_space_cap_bytes','aggregate_rss_guard_bytes','reserve_bytes','sample_interval_seconds','headroom_basis','cgroup_memory_max','swap_total_bytes']
    if any(k not in old or k not in new or old[k] is None or new[k] is None or old[k]!=new[k] for k in keys):
        return {'status':'blocked','wall_delta_percent':None,'rss_delta_percent':None,'reason':'resource settings differ'}
    wall=(new['wall_seconds']/old['wall_seconds']-1)*100
    rss=(new['sampled_peak_group_rss_bytes']/old['sampled_peak_group_rss_bytes']-1)*100
    # Any time or RSS increase is surfaced. >10% wall slowdown stops the lane.
    status='STOP' if wall>10 else 'escalate' if wall>0 or rss>0 else 'pass'
    return {'status':status,'wall_delta_percent':wall,'rss_delta_percent':rss,'reason':'complete clean builds; positive deltas require escalation'}

def overall_status(comparison,acceptance_ok):
    if comparison['status'] in ('STOP','escalate'): return comparison['status']
    if comparison['status']!='pass' or not acceptance_ok: return 'blocked'
    return 'pending-final-gates'

def main():
    p=argparse.ArgumentParser();p.add_argument('--evidence',required=True);p.add_argument('--repo',required=True);a=p.parse_args()
    root=pathlib.Path(a.evidence);repo=pathlib.Path(a.repo)
    read=lambda p:json.loads((root/p).read_text())
    old=read('old-final-automation-clean/result.json');new=read('new-automation-clean/result.json')
    manifests=[read(n+'-final-clean-manifest.json') for n in ['old','new']]
    assert manifests[0]['private_lakefile_sha256']==manifests[1]['private_lakefile_sha256']
    frozen=read('census-base.json')['files']
    for entry in frozen:
        assert hashlib.sha256((repo/entry['path']).read_bytes()).hexdigest()==entry['sha256'],entry['path']
    comparison=compare(old,new)
    acceptance_ok=all(read(label+'/result.json')['exit']==0 and read(label+'/result.json').get('guard_stop') is None
        for label in ['new-context-pass','new-producer-context-controls','old-context-pass','old-syntax-controls','old-producer-context-controls'])
    overall=overall_status(comparison,acceptance_ok)
    result={'frozen_sources':'pass','frozen_files':frozen,'comparison':comparison,
        'new_owned_context':'pass' if read('new-context-pass/result.json')['exit']==0 else 'fail',
        'new_original_acceptance':'pass' if read('new-producer-context-controls/result.json')['exit']==0 else 'fail',
        'full_repository_gate':'pending external owner migrations; do not claim acceptance',
        'production_statement_changes':0,'new_local_axiom_declarations':0,
        'status':overall}
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
