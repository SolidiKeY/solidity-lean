#!/usr/bin/env python3
"""Meaningful rejection controls for the external evidence verifier; no Lean.
A valid format-comparison receipt passes. Corrupt hash, wrong producer and false
independent-replay claims must each be rejected. Temporary fixtures stay off Git.
"""
import argparse,json,os,subprocess,sys,tempfile
from pathlib import Path
from census import ROOT

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--evidence",type=Path,required=True)
    a=ap.parse_args(); evidence=a.evidence.resolve()
    if evidence.is_relative_to(ROOT): raise SystemExit("Use off-Git evidence")
    verifier=ROOT/"scripts/h62/item2/audit-theories/verify_census.py"
    env=os.environ.copy();env["PYTHONDONTWRITEBYTECODE"]="1"
    base=[sys.executable,str(verifier),"--evidence"]
    positive=subprocess.run(base+[str(evidence)],cwd=ROOT,env=env,capture_output=True,text=True)
    assert positive.returncode==0,positive.stderr
    receipt=json.loads((evidence/"census-output-receipt.json").read_text())
    cases=[("changed-output-hash","sha256","0"*64),
           ("wrong-producer","producer_source_transitive_sha256","0"*64),
           ("false-independent-replay","independent_compact_replay",True)]
    results=[]
    for name,key,value in cases:
        with tempfile.TemporaryDirectory(prefix="receipt-control-",dir=evidence) as temp:
            case=Path(temp)
            for source in evidence.iterdir():
                if source==case or source.name=="census-output-receipt.json": continue
                (case/source.name).symlink_to(source,target_is_directory=source.is_dir())
            bad=dict(receipt);bad[key]=value
            (case/"census-output-receipt.json").write_text(json.dumps(bad)+"\n")
            result=subprocess.run(base+[str(case)],cwd=ROOT,env=env,capture_output=True,text=True)
            assert result.returncode==1 and "AssertionError" in result.stderr,(name,result.stdout,result.stderr)
            results.append({"case":name,"exit":result.returncode,"rejected":True})
    complete=["--require-complete-explicit-module","Solidity/Theory/Typed/Obs/Paths.lean",
              "--require-complete-explicit-module","Solidity/Theory/Typed/MemMirror.lean"]
    completed=subprocess.run(base+[str(evidence)]+complete,cwd=ROOT,env=env,capture_output=True,text=True)
    assert completed.returncode==0 and completed.stdout.count("EXPLICIT_MODULE_PASS:")==2,(completed.stdout,completed.stderr)
    module_controls=[]
    for module,marker in [("Solidity/Theory/Typed/Mem.lean","EXPLICIT_MODULE_BLOCKED:"),
                          ("Solidity/Theory/NotMapped.lean","EXPLICIT_MODULE_UNKNOWN:")]:
        result=subprocess.run(base+[str(evidence),"--require-complete-explicit-module",module],cwd=ROOT,env=env,capture_output=True,text=True)
        assert result.returncode==1 and marker in result.stdout,(module,result.stdout,result.stderr)
        module_controls.append({"module":module,"exit":result.returncode,"rejected":True,"decisive":result.stdout.splitlines()[-1]})
    payload={"complete_explicit_module_exit":completed.returncode,"module_rejection_controls":module_controls,"valid_receipt_exit":positive.returncode,"negative_controls":results,"lean_runs":0}
    (evidence/"evidence-controls.json").write_text(json.dumps(payload,indent=2)+"\n")
    print(json.dumps(payload))

if __name__=="__main__": main()
