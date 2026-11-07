#!/usr/bin/env python3
"""Real acceptance/rejection controls for the scoped frozen-file verifier; no Lean."""
import argparse,json,os,subprocess,sys
from pathlib import Path
from census import ROOT

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--evidence",type=Path,required=True)
    a=ap.parse_args();out=a.evidence.resolve()
    if out.is_relative_to(ROOT):raise SystemExit("Use off-Git evidence")
    base=[sys.executable,str(ROOT/"scripts/h62/item2/audit-theories/verify_subset.py"),"--evidence",str(out)]
    selected=["Solidity/Theory/Typed/Obs/Paths.lean","Solidity/Theory/Typed/MemMirror.lean","Solidity/Theory/Bridge/Denote.lean","Solidity/Theory/Progress/Outcome.lean","Solidity/Theory/Mutability/Closer.lean","Solidity/Theory/Mutability/Assignable.lean"]
    positive=subprocess.run(base+sum((["--module",m]for m in selected),[]),capture_output=True,text=True)
    assert positive.returncode==0,(positive.stdout,positive.stderr)
    cases=[("changed-frozen-source",["Solidity/Theory/Progress/Tuple.lean"],"frozen source changed"),
      ("uncovered-statements",["Solidity/Theory/Typed/Mem.lean"],"explicit joint witnesses missing"),
      ("ordinary-impossible-not-H69",["Solidity/Theory/Mutability/Payable.lean"],"1 explicit joint witnesses missing"),
      ("partial-Pure-not-complete",["Solidity/Theory/Mutability/Pure.lean"],"explicit joint witnesses missing"),
      ("outside-map",["../../unmapped.lean"],"outside original frozen module map"),
      ("duplicate-module",[selected[0],selected[0]],"duplicate module")]
    results=[]
    for name,modules,marker in cases:
        result=subprocess.run(base+sum((["--module",m]for m in modules),[]),capture_output=True,text=True)
        text=result.stdout+result.stderr
        assert result.returncode!=0 and "SUBSET_REFUSED:" in text and marker in text,(name,text)
        results.append({"case":name,"exit":result.returncode,"decisive":text.strip()})
    payload={"valid_exit":positive.returncode,"positive":positive.stdout.strip(),"negative_controls":results,"lean_jobs":0}
    (out/"subset-controls.json").write_text(json.dumps(payload,indent=2)+"\n");print(json.dumps(payload))

if __name__=="__main__":main()
