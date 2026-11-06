#!/usr/bin/env python3
"""Fail closed on incomplete/incomparable clean timings; escalate any regression."""
import json, math, sys

def compare(old,new):
    for r in (old,new):
        if r['status']!='pass' or not r['clean'] or r['kind']!='yul': raise ValueError('requires passing CLEAN full Yul reports')
        for k in ['wall_seconds','peak_process_group_rss_bytes']:
            if not math.isfinite(r[k]) or r[k]<=0: raise ValueError('invalid '+k)
        if not r['modules'] or any(m['exit']!=0 or m.get('stop') for m in r['modules']): raise ValueError('incomplete modules')
        for k in ['source_check_before','source_check_after']:
            if r[k]['status']!='pass': raise ValueError('source verification missing/failing')
    for k in ['target_order_sha256','config_policy_sha256','resources','swap_total_kib','reserve_bytes','sampled_rss_budget_bytes','guard_interval_seconds','driver_sha256','resource_helper_sha256','resource_policy']:
        if old[k]!=new[k]: raise ValueError('incomparable '+k)
    if [r['module'] for r in old['modules']] != [r['module'] for r in new['modules']]: raise ValueError('module coverage mismatch')
    wall=(new['wall_seconds']/old['wall_seconds']-1)*100
    rss=(new['peak_process_group_rss_bytes']/old['peak_process_group_rss_bytes']-1)*100
    delta=max(wall,rss)
    exceeds=any(10*new[k]>11*old[k] for k in ['wall_seconds','peak_process_group_rss_bytes'])
    return dict(old_census_sha256=old['census_sha256'],new_census_sha256=new['census_sha256'],wall_delta_percent=wall,rss_delta_percent=rss,status='STOP_GT_10_PERCENT' if exceeds else 'ESCALATE_REGRESSION' if delta>0 else 'pass')
if __name__=='__main__':
    try: result=compare(*(json.load(open(p)) for p in sys.argv[1:3]))
    except (ValueError,KeyError,ZeroDivisionError) as e: print(str(e),file=sys.stderr);sys.exit(1)
    print(json.dumps(result));sys.exit(0 if result['status']=='pass' else 3 if result['status']=='STOP_GT_10_PERCENT' else 2)
