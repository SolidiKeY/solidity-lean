#!/usr/bin/env python3
"""Serial pinned core/vendor input build. External packages are cache-only."""
from pathlib import Path
import os,subprocess,re,json,time,signal,hashlib
root=Path(__file__).resolve().parents[3]; bridge=root/'Bridge'
lean='/workspace/.setup/tools/lean-4.24.0-linux/bin/lean'
env={**os.environ,'PATH':'/workspace/.setup/tools/lean-4.24.0-linux/bin:'+os.environ['PATH'],'XDG_CACHE_HOME':'/workspace/.setup/cache','LEAN_NUM_THREADS':'1'}
search=subprocess.check_output(['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','env','printenv','LEAN_PATH'],cwd=bridge,env=env,text=True).strip()
env['LEAN_PATH']=search
seen=set(); order=[]
def visit(name):
 if name in seen:return
 seen.add(name)
 if name.startswith('Solidity.'):
  p=root/(name.replace('.','/')+'.lean'); cwd=root; output=root/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean'); flags=[]
 elif name.startswith(('EvmYul.','Conform.')):
  p=bridge/'vendor'/(name.replace('.','/')+'.lean'); cwd=bridge; output=bridge/'.lake/build/lib/lean'/(name.replace('.','/')+'.olean'); flags=['--root=vendor']
 else:
  if not any((Path(d)/(name.replace('.','/')+'.olean')).is_file() for d in search.split(':')):
   raise RuntimeError('Missing pinned external cache artifact: '+name)
  return
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for dep in line.split()[1:]: visit(dep)
 order.append((name,p,cwd,output,flags))
for name in ['Solidity.Precompiles.Osaka','EvmYul.EVM.PrecompiledContracts']:visit(name)
out=bridge/'tests/precompile-agreement/evidence'
with (out/'pinned-input-build.log').open('w') as log:
 for i,(name,p,cwd,output,flags) in enumerate(order):
  available=int(re.search(r'MemAvailable:\s+(\d+)',Path('/proc/meminfo').read_text())[1])*1024
  assert available>=4*1024**3
  output.parent.mkdir(parents=True,exist_ok=True)
  cmd=[lean,'-j1','-M11264','--tstack=131072',*flags,'-o',str(output),str(p.relative_to(cwd))]
  log.write(f'{i+1}/{len(order)} SHA256={hashlib.sha256(p.read_bytes()).hexdigest()} CWD={cwd} COMMAND='+ ' '.join(cmd)+'\n'); log.flush()
  start=time.monotonic(); peak=0; minimum=available
  proc=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  while proc.poll() is None:
   try:
    status=Path(f'/proc/{proc.pid}/status').read_text()
    rss=int(re.search(r'VmRSS:\s+(\d+)',status)[1])*1024
    swap=int(re.search(r'VmSwap:\s+(\d+)',status)[1])*1024
    peak=max(peak,rss)
    minimum=min(minimum,int(re.search(r'MemAvailable:\s+(\d+)',Path('/proc/meminfo').read_text())[1])*1024)
    if rss>12*1024**3 or swap or minimum<4*1024**3:
     os.killpg(proc.pid,signal.SIGKILL);log.write('RESOURCE_GUARD_STOP\n')
   except (FileNotFoundError,TypeError):pass
   time.sleep(.1)
  log.write(f'EXIT={proc.returncode} SECONDS={time.monotonic()-start:.3f} PEAK_RSS={peak} MIN_AVAILABLE={minimum}\n');log.flush()
  print(f'{i+1}/{len(order)} {name} exit={proc.returncode}',flush=True)
  if proc.returncode:raise SystemExit(proc.returncode)
 print('PINNED_INPUT_BUILD_PASS',flush=True)
