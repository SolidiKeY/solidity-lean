#!/usr/bin/env python3
"""Matched unchanged-core timings around additive proof checks; no full gate claim."""
import argparse,json,pathlib,statistics,subprocess,sys
p=argparse.ArgumentParser();p.add_argument('--evidence',required=True);p.add_argument('--config',required=True);a=p.parse_args();e=pathlib.Path(a.evidence);root=pathlib.Path(__file__).resolve().parents[4];runner=root/'scripts/h62/item2/audit-evm-compiler/bounded.py'
def checked(label,args):
 out=e/label;r=subprocess.run([sys.executable,str(runner),'--output',str(out),'--','lake','-f',a.config,'env','lean','-j1','--tstack=131072',*args],capture_output=True,text=True)
 if r.returncode:raise SystemExit(r.stdout+r.stderr)
 log=pathlib.Path(str(out)+'.log').read_text()
 if 'sorryAx' in log or 'error:' in log:raise SystemExit('invalid proof artifact '+label)
 return json.loads(pathlib.Path(str(out)+'.json').read_text())['elapsed_seconds']
before=[checked('before-layout-'+str(i),['Solidity/Evm/Layout.lean']) for i in range(3)]
for name in ['LayoutAudit','SuccessAudit','HeadlineAudit']:checked('final-'+name,['tests/h62/item2/audit-evm-compiler/'+name+'.lean'])
after=[checked('after-layout-'+str(i),['Solidity/Evm/Layout.lean']) for i in range(3)]
b=statistics.median(before);c=statistics.median(after);delta=100*(c/b-1);result=dict(before=before,after=after,median_before=b,median_after=c,delta_percent=delta,threshold_percent=10,unchanged_original_sources=True,scope='Original Layout checking around additive helper validation; no root/build-graph change',outcome='pass' if delta<=10 else 'stop-slowdown')
(e/'timings.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));raise SystemExit(int(delta>10))
