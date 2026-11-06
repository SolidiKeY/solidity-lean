#!/usr/bin/env python3
"""Run unchanged run-lean.sh with native 4.24 and serialized Lean children.
The sysroot proxy changes scheduling/diagnostic stack size only; all installed
libraries/binaries are symlinked to the same official 4.24 distribution.
No systemd, swap, proof-option overrides, source/config/root edits or 4.35.
Caller must hold the repository writer lock throughout.
"""
import argparse, json, os, resource, signal, subprocess, time
from pathlib import Path
import bounded_lean

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--toolchain',type=Path,required=True)
 p.add_argument('--artifacts',type=Path,required=True)
 p.add_argument('--probe',action='store_true')
 a=p.parse_args(); repo=Path.cwd(); root=a.artifacts.resolve(); tool=a.toolchain.resolve()
 evidence=root/'evidence'; evidence.mkdir(exist_ok=True)
 proxy=root/'serial-v424-sysroot'; (proxy/'bin').mkdir(parents=True,exist_ok=True)
 for item in tool.iterdir():
  dest=proxy/item.name
  if item.name!='bin' and not dest.exists(): dest.symlink_to(item,target_is_directory=item.is_dir())
 for item in (tool/'bin').iterdir():
  dest=proxy/'bin'/item.name
  if item.name!='lean' and not dest.exists(): dest.symlink_to(item)
 wrapper=proxy/'bin/lean'
 wrapper.write_text('#!/usr/bin/env python3\nimport fcntl,json,subprocess,sys,time\nfrom pathlib import Path\n'
  +f'with open({str(root/"heavy-lean.lock")!r},"a") as lock:\n'
  +' fcntl.flock(lock,fcntl.LOCK_EX)\n'
  +f' with open({str(evidence/"serial-lean-commands.jsonl")!r},"a") as log:\n'
  +'  log.write(json.dumps({"time":time.time(),"args":sys.argv[1:]})+"\\n"); log.flush()\n'
  +f' result=subprocess.run([{str(tool/"bin/lean")!r},"-j1","--tstack=131072",*sys.argv[1:]])\n'
  +' sys.exit(result.returncode)\n')
 wrapper.chmod(0o755)
 env=dict(os.environ,LEAN_NUM_THREADS='1',LAKE_OVERRIDE_LEAN='true',LEAN_SYSROOT=str(proxy),
   PATH=str(proxy/'bin')+':'+str(tool/'bin')+':'+os.environ['PATH'],
   SOLKEY_RULES='/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key')
 versions={name:subprocess.check_output([str(tool/'bin'/name),'--version'],text=True).strip() for name in ['lean','lake']}
 print(json.dumps({'versions':versions}),flush=True)
 if not versions['lean'].startswith('Lean (version 4.24.0,'): raise RuntimeError(versions)
 swap=[x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('SwapTotal:')][0]
 if swap.split()[1]!='0': raise RuntimeError('system swap enabled')
 def run(name,cmd):
  log=evidence/(name+'.log'); start=time.monotonic(); peak=0; concurrency=0; stop=None
  if bounded_lean.available()<4*1024**3: raise RuntimeError("less than 4 GiB startup headroom")
  with log.open('w') as stream:
   proc=subprocess.Popen(cmd,cwd=repo,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=bounded_lean.limits)
   try:
    while proc.poll() is None:
     rss=0; leans=0
     for entry in Path('/proc').iterdir():
      if not entry.name.isdigit(): continue
      try:
       stat=(entry/'stat').read_text(); fields=stat[stat.rfind(')')+2:].split()
       if int(fields[2])!=proc.pid: continue
       rss+=int((entry/'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
       if (entry/'exe').resolve()==tool/'bin/lean': leans+=1
      except (OSError,ValueError): pass
     peak=max(peak,rss); concurrency=max(concurrency,leans)
     if bounded_lean.available()<4*1024**3 or rss>12*1024**3:
      stop='resource-reserve-or-rss'; bounded_lean.terminate(proc); break
     if leans>1: stop='concurrent-heavy-Lean'; bounded_lean.terminate(proc); break
     time.sleep(.2)
   finally: bounded_lean.terminate(proc)
  row={'command':cmd,'exit':proc.returncode,'resource_stop':stop,'wall_seconds':round(time.monotonic()-start,3),
    'sampled_peak_group_rss_bytes':peak,'sampled_peak_heavy_lean_concurrency':concurrency,'log':str(log)}
  (evidence/(name+'.json')).write_text(json.dumps(row,indent=2)+'\n')
  print(json.dumps(row),flush=True)
  if row['exit']!=0 or stop: raise RuntimeError('gate failed: '+name)
  return row
 key=run('keysort-final-v424',[str(wrapper),'--root='+str(repo),'-o',str(root/'KeySort-final-v424.olean'),str(repo/'Solidity/KeySort.lean')])
 probe=run('serial-lake-probe-v424',[str(tool/'bin/lake'),'env','lean','--version'])
 if a.probe: return
 final=run('run-lean-final-v424',['./run-lean.sh'])
 (evidence/'runtime-gate.json').write_text(json.dumps({'status':'pass','versions':versions,'keysort':key,'serial_probe':probe,'final':final},indent=2)+'\n')
 print('RUNTIME_GATE_PASS: '+versions['lean']+'; '+versions['lake']+'; bounded KeySort passed; unchanged ./run-lean.sh passed',flush=True)

if __name__=='__main__':
 signal.signal(signal.SIGTERM,bounded_lean.interrupted); signal.signal(signal.SIGINT,bounded_lean.interrupted)
 main()
