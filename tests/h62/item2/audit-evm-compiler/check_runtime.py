#!/usr/bin/env python3
"""Ensure timeout stops this job tree and missing -j1 is refused."""
import argparse,json,os,pathlib,subprocess,sys
p=argparse.ArgumentParser();p.add_argument('--evidence',required=True);a=p.parse_args();e=pathlib.Path(a.evidence);root=pathlib.Path(__file__).resolve().parents[4];runner=root/'scripts/h62/item2/audit-evm-compiler/bounded.py'
command=[sys.executable,'-c',"import subprocess,time; p=subprocess.Popen(['sleep','60']); print(p.pid,flush=True); time.sleep(60)"]
r=subprocess.run([sys.executable,str(runner),'--seconds','1','--output',str(e/'timeout-control'),'--',*command],capture_output=True,text=True);assert r.returncode==124,r.stdout+r.stderr
pid=int((e/'timeout-control.log').read_text().strip());state=pathlib.Path('/proc')/str(pid)/'stat'
assert not state.exists() or state.read_text().rsplit(')',1)[1].split()[0]=='Z','timeout left running child'
# This is a fake process name, not a Lean invocation.
command=['bash','-c',"exec -a lean python3 -c 'import time; time.sleep(5)'"]
r=subprocess.run([sys.executable,str(runner),'--output',str(e/'j1-control'),'--',*command],capture_output=True,text=True);assert r.returncode==125,r.stdout+r.stderr
assert json.loads((e/'j1-control.json').read_text())['stop_reason']=='Lean process without explicit -j1'
print('PASS timeout process-tree cleanup and missing-j1 refusal controls')
