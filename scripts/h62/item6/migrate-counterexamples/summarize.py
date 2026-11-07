#!/usr/bin/env python3
"""Reproduce the off-git dependency, interface and measurement receipts."""
import hashlib, json, os, re, subprocess
from pathlib import Path
import census
AREA=Path("/workspace/h62-migrate-counterexamples");E=AREA/"evidence"
def write(name,x): (E/name).write_text(json.dumps(x,indent=2,ensure_ascii=False)+"\n")
def load(name):return json.loads((E/name).read_text())
def digest(path):
 with path.open("rb") as f:return hashlib.file_digest(f,"sha256").hexdigest()
x=census.inspect();write("census.json",x)
inputs=Path("/workspace/h62-coordinator-inputs")
checks={f:digest(inputs/f)==h for f,h in json.loads((inputs/"sha256.json").read_text()).items()}
assert all(checks.values())
pin=json.loads((inputs/"toolchain-pin.json").read_text());assert digest(AREA/pin["asset"])==pin["sha256"]
write("toolchain-receipt.json",{"coordinator_inputs_verified":checks,"pin":pin,"target_archive_sha256":digest(AREA/pin["asset"]),"old_archive_sha256":digest(Path("/workspace/.setup/tools/lean-4.24.0-linux.tar.zst")),"target_lean_binary_sha256":digest(AREA/"lean-4.35.0-linux/bin/lean"),"target_lake_binary_sha256":digest(AREA/"lean-4.35.0-linux/bin/lake")})
old=load("old-clean-2/result.json");new=load("new-clean-1/result.json")
oldmap={m['module']:m for m in old['modules']}
partial=[]
for m in new['modules']:
 if m['exit']==0:
  b=oldmap[m['module']]
  partial.append({"module":m['module'],"old_wall_s":b['wall_s'],"new_wall_s":m['wall_s'],"wall_delta_percent":100*(m['wall_s']/b['wall_s']-1),"old_max_child_rss_kib":b['max_rss_kib'],"new_max_child_rss_kib":m['max_rss_kib'],"rss_delta_percent":100*(m['max_rss_kib']/b['max_rss_kib']-1)})
write("partial-metrics.json",{"boundary":"Matched completed modules only; no full directory timing/RSS conclusion. Any positive delta requires escalation; observed RSS deltas exceed 10%.","modules":partial})
def typeblocks(path):
 blocks={};name=None
 for line in path.read_text().splitlines():
  if line.removeprefix("@").startswith("Solidity.Counterexamples."):
   name=line.split(" :",1)[0].removeprefix("@");blocks[name]=[]
  elif line.startswith("'Solidity."):name=None
  if name is not None:blocks[name].append(line)
 return {name:"\n".join(lines)+"\n" for name,lines in blocks.items()}
interfaces={}
for label,probe in [("old-probes-2","FrozenInterfaces"),("old-probes-2","OverlapInterfaces"),("new-probes","OverlapInterfaces")]:
 path=E/label/(probe+".log");blocks=typeblocks(path)
 dest=E/label/(probe+".types.txt");dest.write_text("".join(blocks.values()))
 interfaces[label+"/"+probe]={"raw_log_sha256":digest(path),"rendered_types_sha256":digest(dest),"declarations":{name:hashlib.sha256(body.encode()).hexdigest() for name,body in blocks.items()}}
assert len(interfaces['old-probes-2/FrozenInterfaces']['declarations'])==18
oldtypes=interfaces['old-probes-2/OverlapInterfaces']['declarations'];newtypes=interfaces['new-probes/OverlapInterfaces']['declarations']
assert oldtypes==newtypes and len(oldtypes)==2
write("frozen-interfaces.json",{"source_files":x['files'],"rendered_elaborated_types":interfaces,"overlap_rendered_types_equal":True,"boundary":"Source SHA256 freezes exact bytes. Rendered type hashes are pretty-printer output, not canonical kernel Expr hashes. Only two named types have target evidence; the other sixteen await dependencies. Raw axiom logs differ only by Quot.sound.{u} printing."})
ownership=json.loads((inputs/"ownership.json").read_text())['items']
def owners(path):return [v['owner'] for v in ownership if path in [s.strip() for s in v.get('writeScope','').split(';')]]
errors=[]
for m in new['modules']:
 if m['exit'] not in (0,None):
  text=(E/'new-clean-1'/(m['module']+'.log')).read_text()
  for match in re.finditer(r"^error: ([^:]+):(\d+):(\d+): (.*)$",text,re.M):
   path,line,col,message=match.groups();errors.append({"path":path,"line":int(line),"column":int(col),"message":message,"owners":owners(path)})
write("dependency-report.json",{"base":census.BASE,"target_toolchain":pin,"primary_errors":errors,"assigned_modules":[m for m in new['modules'] if m['module'].startswith('Solidity.Counterexamples.')],"cross_directory_dependencies":[{"module":m,"path":m.replace('.','/')+'.lean',"owners":owners(m.replace('.','/')+'.lean')} for m in x['external_dependencies']],"toolchain_imports":[m for m,deps in x['import_graph'].items() if deps is None],"request":{"id":"DEP-SYNTAX-RAW-01","owner":"solidity-h62-6-20261106/migrate-syntax","relay":"solidity-h62-6-20261106/migrate-root-gate","exact_files":["Solidity/Syntax/Raw.lean"],"action":"Supply owner-reviewed migration overlay for the five String/Slice errors, preserving frozen semantics/budgets; then relay the dependency closure for three blocked roots. No out-of-scope edits made by this lane."}})
cmds=[["git","rev-parse","HEAD"],["git","merge-base","--is-ancestor",census.BASE,"HEAD"],["git","merge-base","--is-ancestor",census.BASE,"origin/master"]]
receipts=[]
for cmd in cmds:
 r=subprocess.run(cmd,cwd=census.ROOT,text=True,capture_output=True);assert r.returncode==0;receipts.append({"command":cmd,"exit":r.returncode,"stdout":r.stdout})
write("setup-receipt.json",{"repository":str(census.ROOT),"branch":subprocess.check_output(["git","branch","--show-current"],cwd=census.ROOT,text=True).strip(),"base":census.BASE,"git_receipts":receipts,"affinity_cpus":sorted(os.sched_getaffinity(0)),"selected_cpu":old['cpu'],"memory_max":Path('/sys/fs/cgroup/memory.max').read_text().strip(),"memory_swap_max":Path('/sys/fs/cgroup/memory.swap.max').read_text().strip(),"proc_swaps":Path('/proc/swaps').read_text(),"private_lakefile_sha256":{"old":digest(AREA/'old-clean-2/lakefile.toml'),"new":digest(AREA/'new-clean-1/lakefile.toml')}})
write("historical-attempts.json",{"old-clean-1":{"status":"launch-failed","cause":"/usr/bin/time absent; no Lean job started; legacy result status was left running. Superseded by valid wait4-based old-clean-2."},"old-probes":{"status":"failed","cause":"Unknown option pp.width in two probe files. Changed only to format.width; all probes pass in old-probes-2."}})
print("receipts generated")
