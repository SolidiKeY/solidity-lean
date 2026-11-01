#!/usr/bin/env python3
"""Freshly check the entire original Derived17 workload. Wrap in a 300s guard.
Existing prerequisite Lake setups are required; group outputs never reused.
"""
import argparse, pathlib, subprocess, json, time, hashlib, os
p=argparse.ArgumentParser();p.add_argument('--output',required=True);p.add_argument('--results',required=True);a=p.parse_args()
r=pathlib.Path(__file__).resolve().parent.parent;d=pathlib.Path(a.output);d.mkdir(exist_ok=False)
modules=['Solidity.Calculus.MemoryLoopReplay']+['Solidity.TestSuite.MemoryLoopReplay.'+kind+f'{i:02}' for kind in ['Discover','Assemble'] for i in range(10)]+['Solidity.TestSuite.Derived17MemoryLoop','Solidity.TestSuite.MemoryLoopReplay.Refusals','Solidity.TestSuite.Derived17']
rows=[];arts={};start=time.monotonic();env=os.environ.copy();env['LEAN_NUM_THREADS']='1'
def save(code):
 pathlib.Path(a.results).write_text(json.dumps(dict(kind='fresh-original-Derived17-workload',budgetSeconds=300,exit_code=code,seconds=time.monotonic()-start,expectedModules=modules,checks=rows),indent=2)+'\n')
save(None)
for module in modules:
 path=module.replace('.','/');setup=json.loads((r/('.lake/build/ir/'+path+'.setup.json')).read_text());setup['importArts'].update(arts)
 sp=d/(module+'.setup.json');sp.write_text(json.dumps(setup));source=r/(path+'.lean');log=d/(module+'.log');out=d/(module+'.olean')
 cmd=['lean','-j1','--tstack=32768','--setup',str(sp),str(source),'-o',str(out),'-c',str(d/(module+'.c'))]
 (d/(module+'.source.lean')).write_bytes(source.read_bytes())
 t=time.monotonic()
 with log.open('wb') as stream:code=subprocess.run(cmd,cwd=r,env=env,stdout=stream,stderr=subprocess.STDOUT).returncode
 rows.append(dict(module=module,source=str(source),sourceSha256=hashlib.sha256(source.read_bytes()).hexdigest(),command=cmd,exit_code=code,seconds=time.monotonic()-t,log=str(log),output=str(out),fresh=True));save(code if code else None)
 print(module,code,rows[-1]['seconds'],flush=True)
 if code:raise SystemExit(code)
 arts[module]=[str(out)]
final_code=1 if time.monotonic()-start>300 else 0
save(final_code)
raise SystemExit(final_code)
