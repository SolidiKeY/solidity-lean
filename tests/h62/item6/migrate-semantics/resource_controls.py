#!/usr/bin/env python3
"""OS-backed controls for cap enforcement, per-child RSS and owned timeout cleanup."""
import argparse,json,os,sys,time,signal
from pathlib import Path
root=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(root/'scripts/h62/item6/migrate-semantics'))
from bounded import run,settings,MODULE_CAP_BYTES,passed
ap=argparse.ArgumentParser(); ap.add_argument('--out',type=Path,required=True); a=ap.parse_args(); a.out.mkdir(parents=True,exist_ok=False)
rows=[]
def check(label,code,**kwargs):
    result=run([sys.executable,'-c',code],log=a.out/(label+'.log'),env=dict(os.environ),**kwargs)
    rows.append({'label':label,**result}); return result
r=check('cap-and-allocation','import resource,json; print(json.dumps(resource.getrlimit(resource.RLIMIT_AS))); data=bytearray(32*1024**2)')
assert r['exit']==0 and r['stop'] is None
assert json.loads((a.out/'cap-and-allocation.log').read_text())==[MODULE_CAP_BYTES,MODULE_CAP_BYTES]
assert r['peak_rss_kib']>=32*1024
small=check('small-child','pass'); assert small['exit']==0 and small['peak_rss_kib']<r['peak_rss_kib']
limited=check('oversize-denied','try:\n data=bytearray(9*1024**3)\nexcept MemoryError:\n print("denied")\nelse:\n raise SystemExit("cap failed")')
assert limited['exit']==0 and (a.out/'oversize-denied.log').read_text().strip()=='denied'
timed=check('owned-timeout','import time; time.sleep(10)',timeout_seconds=.3)
assert timed['exit']==-9 and timed['stop']=='TEST_TIMEOUT' and timed['wall_seconds']<3
assert not passed({'exit':0,'stop':'RESOURCE_BLOCK'})
assert not passed({'exit':0,'stop':'MODULE_300S_STOP'})
assert passed({'exit':0,'stop':None})
desc=check('normal-leader-descendant','import subprocess,sys; p=subprocess.Popen([sys.executable,"-c","import time; time.sleep(10)"]); print(p.pid,flush=True)')
assert passed(desc)
pid=int((a.out/'normal-leader-descendant.log').read_text().strip())
def child_state():
    try: return Path('/proc/'+str(pid)+'/stat').read_text().split(') ',1)[1].split()[0]
    except FileNotFoundError: return None
for _ in range(20):
    if child_state() in [None,'Z']: break
    time.sleep(.1)
if child_state() not in [None,'Z']:
    try: os.kill(pid,signal.SIGKILL)
    except ProcessLookupError: pass
    raise AssertionError('owned descendant survived normal leader completion')
(a.out/'result.json').write_text(json.dumps({'settings':settings(),'status':'pass','rows':rows,'stop_exit0_rejected':True,'normal_descendant_cleaned':True},indent=2)+'\n')
print('PASS:8GiB cap, allocation refusal, per-child RSS, timeout and normal-descendant cleanup, stop/exit race policy')
