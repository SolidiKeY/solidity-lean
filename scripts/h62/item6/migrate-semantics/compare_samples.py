#!/usr/bin/env python3
"""Compare matching successful incremental samples; never a full clean gate."""
import argparse,json
from pathlib import Path
from bounded import passed,settings
ap=argparse.ArgumentParser(); ap.add_argument('--old',type=Path,required=True); ap.add_argument('--new',type=Path,required=True); ap.add_argument('--out',type=Path,required=True); a=ap.parse_args()
old=json.loads((a.old/'summary.json').read_text()); new=json.loads((a.new/'summary.json').read_text())
x=json.loads((a.old/'census.json').read_text()); y=json.loads((a.new/'census.json').read_text())
if x['closure_sha256']!=y['closure_sha256']: raise SystemExit('SOURCE_MISMATCH')
if old['settings']!=new['settings']: raise SystemExit('SETTINGS_MISMATCH')
if old['settings']!=settings(): raise SystemExit('H78_SETTINGS_MISMATCH')
if not old['rows'] or [r['module'] for r in old['rows']]!=[r['module'] for r in new['rows']]: raise SystemExit('MODULE_ORDER_MISMATCH')
rows=[]
for before,after in zip(old['rows'],new['rows']):
    if not passed(before) or not passed(after): raise SystemExit('INCOMPLETE_SAMPLE')
    rows.append({'module':before['module'],'old_wall_seconds':before['wall_seconds'],'new_wall_seconds':after['wall_seconds'],'old_peak_rss_kib':before['peak_rss_kib'],'new_peak_rss_kib':after['peak_rss_kib'],'wall_delta_percent':100*(after['wall_seconds']/before['wall_seconds']-1),'rss_delta_percent':100*(after['peak_rss_kib']/before['peak_rss_kib']-1)})
report={'boundary':'Matched incremental affected-module checks on identical migrated source tree. Not a full clean build comparison.','old_lean':old['lean'],'new_lean':new['lean'],'old_evidence':str(a.old),'new_evidence':str(a.new),'settings':old['settings'],'rows':rows,'old_total_wall_seconds':sum(r['old_wall_seconds'] for r in rows),'new_total_wall_seconds':sum(r['new_wall_seconds'] for r in rows),'old_max_module_peak_rss_kib':max(r['old_peak_rss_kib'] for r in rows),'new_max_module_peak_rss_kib':max(r['new_peak_rss_kib'] for r in rows),'memory_policy':'H78: continue despite memory increases within 8GiB per-process address-space cap; include growth at human cut-over.'}
a.out.write_text(json.dumps(report,indent=2)+'\n'); print(json.dumps(report,indent=2))
