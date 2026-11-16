#!/usr/bin/env python3
"""Two opt-in probes of an existing consumer, or offline verification; no Lake build.
python3 docs/audits/direction-tools/mutation/consumer_probe.py --run --lean LEAN --out EXTERNAL_DIR
python3 docs/audits/direction-tools/mutation/consumer_probe.py --verify --out EXTERNAL_DIR
"""
import argparse,fcntl,hashlib,json,os,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
from base_tree import BASE,ROOT,read_base_blobs
OUT=Path(__file__).resolve().parent
CAP=12*1024**3
CLOSERS="Solidity/Calculus/Closers.lean";CONSUMER="Solidity/Examples/Tactics/CheckedBlock.lean"
def sha(data):return hashlib.sha256(data).hexdigest()
def sources():
 blobs=read_base_blobs([CLOSERS,CONSUMER]);text=blobs[CONSUMER].decode();sections=[];bindings=[]
 for start,end in [("namespace Solidity.Examples.Tactics.CheckedBlock","/-! ## 1"),("theorem underflowChecked","/-! What the block writes")]:
  assert text.count(start)==1;begin=text.index(start);finish=text.index(end,begin+len(start));part=text[begin:finish];sections.append(part)
  bindings.append(dict(path=CONSUMER,line=text[:begin].count("\n")+1,start=start,end=end,sha256=sha(part.encode())))
 baseline="import Solidity.Calculus.Surface\n"+blobs[CLOSERS].decode()+"\n"+"".join(sections)+"\nend Solidity.Examples.Tactics.CheckedBlock\n"
 old="| .error .panic => true";assert baseline.count(old)==1
 return baseline,baseline.replace(old,"| .error .panic => false",1),bindings

def main():
 ap=argparse.ArgumentParser();mode=ap.add_mutually_exclusive_group(required=True);mode.add_argument("--run",action="store_true");mode.add_argument("--verify",action="store_true");ap.add_argument("--lean",type=Path);ap.add_argument("--out",type=Path,required=True);a=ap.parse_args()
 baseline,mutant,bindings=sources();external=a.out.resolve();assert not external.is_relative_to(ROOT)
 cache_bytes=(OUT/"cache-verification.json").read_bytes();cache=json.loads(cache_bytes);assert cache["base"]==BASE and cache["status"]=="pass"
 if a.verify:
  r=json.loads((OUT/"consumer-probe.json").read_text());assert r["base"]==BASE and r["total_elaborations"]<=10 and r["source_bindings"]==bindings
  assert r["cache_receipt_sha256"]==sha(cache_bytes)
  for row,expected in [(r["baseline"],baseline),(r["mutant"],mutant)]:
   assert Path(row["source_path"]).read_bytes()==expected.encode() and sha(expected.encode())==row["source_sha256"]
   assert Path(row["log"]).read_text()[-5000:]==row["output"]
  assert r["baseline"]["returncode"]==0
  ledger=json.loads((a.out/"attempts.json").read_text());assert r["total_elaborations"]<=len(ledger)<=10
  assert r["baseline"] in ledger[:r["total_elaborations"]] and r["mutant"] in ledger[:r["total_elaborations"]]
  m=r["mutant"];failed=m["returncode"]==1 and "decide" in m["output"] and ("false" in m["output"] or "failed" in m["output"])
  outcome="existing-consumer-proof-failed" if failed else "existing-consumer-survived" if m["returncode"]==0 else "inconclusive"
  assert r["outcome"]==outcome and r["effective_lean_path"]==cache["cache_root"]
  for row in [r["baseline"],m]:assert "--as="+str(CAP) in row["command"] and "-j1" in row["command"]
  print(json.dumps({"base":BASE,"total_elaborations":r["total_elaborations"],"outcome":r["outcome"],"new_elaborations":0},sort_keys=True));return
 assert a.lean is not None;version=subprocess.check_output([str(a.lean),"--version"],text=True).strip();assert "4.24.0" in version
 key=json.loads((OUT/"lean-whole.json").read_text())["keysort"];assert key["returncode"]==0
 policy_commit=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip();assert b"H232" in subprocess.check_output(["git","show",policy_commit+":docs/refactoring-progress.md"],cwd=ROOT)
 common=Path(subprocess.check_output(["git","rev-parse","--git-common-dir"],cwd=ROOT,text=True).strip());common=common if common.is_absolute() else ROOT/common
 lease=(common/"direction-mutation-lean-budget.lock").open("a");fcntl.flock(lease.fileno(),fcntl.LOCK_EX|fcntl.LOCK_NB)
 budget=common/"direction-mutation-lean-budget.json";attempts=json.loads(budget.read_text());assert len(attempts)+2<=10
 for relative,digest in cache["artifacts"].items():assert sha((Path(cache["cache_root"])/relative).read_bytes())==digest
 assert "SwapTotal:             0 kB" in Path("/proc/meminfo").read_text() or int(next(l for l in Path("/proc/meminfo").read_text().splitlines() if l.startswith("SwapTotal:")).split()[1])==0
 external.mkdir(parents=True,exist_ok=True);ledger=external/"attempts.json";env=dict(os.environ,LEAN_NUM_THREADS="1",LEAN_PATH=cache["cache_root"])
 def save():
  temp=budget.with_suffix(".json.tmp");temp.write_text(json.dumps(attempts,indent=2)+"\n");os.replace(temp,budget);ledger.write_text(json.dumps(attempts,indent=2)+"\n")
 def run(name,text):
  assert len(attempts)<10;path=external/("Attempt"+str(len(attempts)+1)+"_"+name+".lean");path.write_text(text)
  command=["prlimit","--as="+str(CAP),"--",str(a.lean.resolve()),"-j1","-M11000","--tstack=131072","--root="+str(external),"-o",str(path.with_suffix(".olean")),str(path)]
  row=dict(name=name,source_path=str(path),source_sha256=sha(text.encode()),command=command);attempts.append(row);save()
  try:
   process=subprocess.run(command,cwd=external,env=env,capture_output=True,text=True,timeout=180);code=process.returncode;output=process.stdout+process.stderr
  except subprocess.TimeoutExpired as e:code=None;output="timeout after 180 seconds: "+str(e)
  log=path.with_suffix(".log");log.write_text(output);row.update(returncode=code,output=output[-5000:],log=str(log));save();print(name+": exit="+str(code)+" "+output[-1800:],flush=True);return row
 b=run("ConsumerBaseline",baseline);m=run("ConsumerM31",mutant) if b["returncode"]==0 else None
 failed=m is not None and m["returncode"]==1 and "decide" in m["output"] and ("false" in m["output"] or "failed" in m["output"])
 outcome="existing-consumer-proof-failed" if failed else "existing-consumer-survived" if m is not None and m["returncode"]==0 else "inconclusive"
 result=dict(base=BASE,versions=dict(lean=version),keysort=key,policy_commit=policy_commit,limitation="no systemd scope on the cloud VM (H232)",total_elaborations=len(attempts),cache_receipt_sha256=sha(cache_bytes),effective_lean_path=env["LEAN_PATH"],source_bindings=bindings,baseline=b,mutant=m,outcome=outcome,boundary="Exact existing underflowChecked declaration and its local instance/scoped-notation context appended to exact full BASE Closers source; no new theorem statement or premise. Only this consumer proof-script coupling is checked; no claim its final statement became false, no project-wide score, and no fresh differential run.")
 data=json.dumps(result,indent=2,sort_keys=True)+"\n";assert len(data.encode())<1000000;(OUT/"consumer-probe.json").write_text(data)
if __name__=="__main__":main()
