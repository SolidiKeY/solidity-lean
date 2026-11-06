#!/usr/bin/env python3
"""One bounded serial Lean check. Arguments: SOURCE LOG [OUTPUT_OLEAN]."""
from pathlib import Path
import os,re,signal,subprocess,sys,time
source,logfile,*output=sys.argv[1:]
cmd=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','env','lean','-j1','-M11264','--tstack=131072']
if output:
 Path(output[0]).parent.mkdir(parents=True,exist_ok=True)
 cmd+=['-o',output[0]]
cmd+=[source]
def stats(pid):
 rss=swap=0
 todo=[pid]
 while todo:
  current=todo.pop()
  try:
   s=Path(f'/proc/{current}/status').read_text()
   rss+=int(re.search(r'VmRSS:\s+(\d+)',s)[1])*1024
   swap+=int(re.search(r'VmSwap:\s+(\d+)',s)[1])*1024
   for task in Path(f'/proc/{current}/task').iterdir():
    todo += [int(x) for x in (task/'children').read_text().split()]
  except (FileNotFoundError,TypeError): pass
 return rss,swap
start=time.monotonic(); peak=0; minimum=2**63; stopped=False
with Path(logfile).open('w') as log:
 log.write('CWD: '+str(Path.cwd())+'\nCOMMAND: '+' '.join(cmd)+'\n');log.flush()
 p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,
   env={**os.environ,'LEAN_NUM_THREADS':'1','PATH':'/workspace/.setup/tools/lean-4.24.0-linux/bin:'+os.environ['PATH']})
 while p.poll() is None:
  rss,swap=stats(p.pid);peak=max(peak,rss)
  available=int(re.search(r'MemAvailable:\s+(\d+)',Path('/proc/meminfo').read_text())[1])*1024
  minimum=min(minimum,available)
  if rss>12*1024**3 or swap or available<4*1024**3:
   os.killpg(p.pid,signal.SIGKILL);stopped=True
  time.sleep(.1)
 log.write(f'EXIT={p.returncode} SECONDS={time.monotonic()-start:.3f} PEAK_RSS={peak} MIN_AVAILABLE={minimum} RESOURCE_STOP={stopped}\n')
print(Path(logfile).read_text(),end='')
raise SystemExit(p.returncode)
