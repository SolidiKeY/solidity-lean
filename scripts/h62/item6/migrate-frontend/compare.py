#!/usr/bin/env python3
"""Fail-closed timing comparison; never treats an incomplete build as faster."""
import argparse
from decimal import Decimal, InvalidOperation
import json
from pathlib import Path

def compare(old,new):
    def complete(x):
        rows=x.get('results',[]);targets=x.get('targets',[])
        return (isinstance(rows,list) and isinstance(targets,list)
                and all(isinstance(t,str) and t for t in targets) and len(set(targets))==len(targets)
                and all(isinstance(r,dict) for r in rows)
                and x.get('status')=='pass' and bool(targets) and len(rows)==len(targets)
                and [r.get('module') for r in rows]==targets
                and all(r.get('exit')==0 and r.get('stop') is None for r in rows))
    reason=None
    if not complete(old) or not complete(new): reason='Both measurements must be complete passing builds'
    elif old['targets']!=new['targets']: reason='Target sets/order differ'
    elif not isinstance(old.get('settings'),dict) or not old.get('settings') or old.get('settings')!=new.get('settings'): reason='Fixed resource/cache settings differ'
    if reason is None:
        try:
            metrics=[Decimal(str(x.get(k,''))) for x in (old,new) for k in ('wall_seconds','peak_group_rss_bytes_sampled')]
            if any(not v.is_finite() or v<=0 for v in metrics): reason='Invalid non-finite/non-positive wall/RSS measurements'
        except (InvalidOperation,ValueError,TypeError): reason='Invalid malformed wall/RSS measurements'
    if reason:
        return {'status':'blocked','reason':reason,'old_rows':len(old.get('results',[])),
                'new_rows':len(new.get('results',[])),'wall_delta_percent':None,'rss_delta_percent':None},2
    wall=(Decimal(str(new['wall_seconds']))/Decimal(str(old['wall_seconds']))-1)*100
    rss=(Decimal(str(new['peak_group_rss_bytes_sampled']))/Decimal(str(old['peak_group_rss_bytes_sampled']))-1)*100
    if wall>10:status,exit_code='STOP_WALL_REGRESSION_GT_10_PERCENT',3
    elif wall>0 or rss>0:status,exit_code='ESCALATE_REGRESSION',1
    else:status,exit_code='performance_pass',0
    return {'status':status,'wall_delta_percent':str(wall),'rss_delta_percent':str(rss),
            'semantics_gate':'Not established by this performance calculation'},exit_code

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--old',type=Path,required=True);ap.add_argument('--new',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args();data,code=compare(json.loads(a.old.read_text()),json.loads(a.new.read_text()))
    a.out.write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(data));raise SystemExit(code)

if __name__=='__main__':main()
