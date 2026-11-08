#!/usr/bin/env python3
"""Opt-in bounded Lean probes; no Lake builds or project source writes.
python3 docs/audits/direction-tools/mutation/lean_probe.py --run --lean LEAN --cache CACHE --out EXTERNAL_DIR
Exact source slices measure only local theorem coupling, never a whole-module/project mutation score.
"""
import argparse,fcntl,hashlib,json,os,re,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
from base_tree import BASE,ROOT,read_base_blobs
OUT=Path(__file__).resolve().parent
CAP=12*1024**3

def digest(data):return hashlib.sha256(data).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument("--run",action="store_true",required=True);ap.add_argument("--lean",type=Path,required=True);ap.add_argument("--cache",type=Path,required=True);ap.add_argument("--out",type=Path,required=True);a=ap.parse_args()
 external=a.out.resolve();assert not external.is_relative_to(ROOT);external.mkdir(parents=True,exist_ok=True)
 assert int(re.search(r"SwapTotal:\s+(\d+)",Path("/proc/meminfo").read_text())[1])==0,"no-swap VM required"
 version=subprocess.check_output([str(a.lean),"--version"],text=True).strip();assert "4.24.0" in version
 lake=subprocess.check_output([str(a.lean.parent/"lake"),"--version"],text=True).strip()
 ledger=external/"attempts.json"
 common=Path(subprocess.check_output(["git","rev-parse","--git-common-dir"],cwd=ROOT,text=True).strip())
 if not common.is_absolute():common=ROOT/common
 lease=(common/"direction-mutation-lean-budget.lock").open("a")
 try:fcntl.flock(lease.fileno(),fcntl.LOCK_EX|fcntl.LOCK_NB)
 except BlockingIOError:raise SystemExit("another probe holds the shared ten-elaboration budget lease")
 budget=common/"direction-mutation-lean-budget.json"
 attempts=json.loads(budget.read_text()) if budget.exists() else json.loads(ledger.read_text()) if ledger.exists() else []
 def save_budget():
  temporary=budget.with_suffix(".json.tmp");temporary.write_text(json.dumps(attempts,indent=2)+"\n");os.replace(temporary,budget)
 save_budget()
 paths=["Solidity/KeySort.lean","Solidity/Update.lean","Solidity/Semantics/Run.lean","Solidity/Semantics/RunFrame.lean","Solidity/Calculus/Logic.lean","Solidity/Calculus/Closers.lean"]
 blobs=read_base_blobs(paths);source={p:b.decode() for p,b in blobs.items()};bindings=[]
 def block(path,start,end):
  text=source[path];assert text.count(start)==1;begin=text.index(start);finish=text.index(end,begin+len(start));part=text[begin:finish]
  bindings.append(dict(path=path,line=text[:begin].count("\n")+1,sha256=digest(part.encode()),start=start,end=end));return part
 modality=block("Solidity/Update.lean","inductive Modality where","/-- What a modality")
 halt=block("Solidity/Semantics/Run.lean","inductive THalt where","/-- A revert with the data")
 alias="abbrev TRes (α : Type) := Except THalt α";assert source["Solidity/Semantics/Run.lean"].count(alias)==1
 bindings.append(dict(path="Solidity/Semantics/Run.lean",sha256=digest(alias.encode()),text=alias))
 onhalt=block("Solidity/Semantics/RunFrame.lean","def _root_.Solidity.Modality.onTHalt","theorem tbind_ok_inv")
 after=block("Solidity/Calculus/Logic.lean","def _root_.Solidity.Modality.afterRunTR","/-- The state a modality")
 tail=block("Solidity/Calculus/Closers.lean","/-- The typed outcome is a panic.","end Solidity")
 fixture="import Lean\nnamespace Solidity\n"+modality+halt+alias+"\n"+onhalt+after+tail+"\nend Solidity\n"
 env=dict(os.environ,LEAN_NUM_THREADS="1",LEAN_PATH=str(a.cache.resolve()))
 def run(name,text):
  assert len(attempts)<10,"audit lifetime ten-elaboration budget exhausted"
  path=external/("Attempt"+str(len(attempts)+1)+"_"+name+".lean");path.write_text(text)
  cmd=["prlimit","--as="+str(CAP),"--",str(a.lean.resolve()),"-j1","-M11000","--tstack=131072","--root="+str(external),"-o",str(path.with_suffix(".olean")),str(path)]
  row=dict(name=name,source_path=str(path),command=cmd,source_sha256=digest(text.encode()));attempts.append(row);ledger.write_text(json.dumps(attempts,indent=2)+"\n");save_budget()
  try:
   r=subprocess.run(cmd,cwd=external,env=env,text=True,capture_output=True,timeout=180);code=r.returncode;output=r.stdout+r.stderr
  except subprocess.TimeoutExpired as e:
   code=None;output="timeout after 180 seconds\n"+str(e)
  log=path.with_suffix(".log");log.write_text(output)
  row.update(returncode=code,output=output[-5000:],log=str(log));ledger.write_text(json.dumps(attempts,indent=2)+"\n");save_budget()
  print(name+": exit="+str(code)+" "+output[-500:],flush=True);return row
 policy_path="docs/refactoring-progress.md";policy_commit=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()
 policy=subprocess.check_output(["git","show",policy_commit+":"+policy_path],cwd=ROOT);assert b"H232" in policy
 key=run("KeySort",source["Solidity/KeySort.lean"])
 assert key["returncode"]==0,"KeySort baseline failed; no runtime pass or mutation inference"
 original=run("ClosersOriginal",source["Solidity/Calculus/Closers.lean"])
 baseline=run("CloserSliceBaseline",fixture)
 results=[]
 if baseline["returncode"]==0:
  for ident,old,new in [("M31","| .error .panic => true","| .error .panic => false"),("M32","| .error .exhausted => false","| .error .exhausted => true")]:
   assert fixture.count(old)==1
   row=run("CloserSlice"+ident,fixture.replace(old,new,1))
   # Missing imports, timeout, resource or syntax errors are never semantic kills.
   proof_failure=row["returncode"]==1 and "unsolved goals" in row["output"]
   status="selected-source-slice-survived" if row["returncode"]==0 else "selected-source-slice-proof-failed" if proof_failure else "inconclusive"
   results.append(dict(id=ident,status=status,probe=row,interpretation="vacuous-premise: isPanic becomes always false, so hp cannot hold; no global panic-coverage conclusion" if ident=="M31" else "local exhausted-case theorem constraint: changed isFail makes the copied theorem proof fail"))
 result=dict(base=BASE,versions=dict(lean=version,lake=lake),policy=dict(id="H232",commit=policy_commit,path=policy_path,sha256=digest(policy),limitation="no systemd scope on the cloud VM (H232)"),memory_address_space_cap_bytes=CAP,swap_total_kib=0,total_elaborations=len(attempts),keysort=key,original_module_baseline=original,source_slice_baseline=baseline,source_slice_bindings=bindings,source_slice_mutants=results,source_slice_counts=dict(proof_failed=sum(r["status"]=="selected-source-slice-proof-failed" for r in results),survived=sum(r["status"]=="selected-source-slice-survived" for r in results),inconclusive=sum(r["status"]=="inconclusive" for r in results)),runtime_gate_pass=False,boundary="Unmodified theorem/definition source blocks copied from BASE into standalone Lean-import fixtures; only local source-slice proof coupling measured. Original module uses existing import cache and may be unavailable. No project build, whole-project survivor claim, fresh differential run, or full source/cache validation.")
 data=json.dumps(result,indent=2,sort_keys=True)+"\n";assert len(data.encode())<1000000;(OUT/"lean-probes.json").write_text(data)
if __name__=="__main__":main()
