#!/usr/bin/env python3
"""Leaf progress complete-module gate: the designated whole-law input packet is required.
Run from the exact frozen validation overlay. All mutation fixtures are off Git;
negative axiom logs are untrusted test inputs, never accepted proof evidence.
"""
import argparse,fcntl,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
from census import ROOT,BASE
from run_frozen_history import LOCK
REQUIRED="Solidity.Theory.Progress.builtinExt_sound"
MODULE="Solidity/Theory/Progress/Leaves.lean"
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ("evidence","out"):ap.add_argument("--"+name,type=Path,required=True)
    a=ap.parse_args();evidence=a.evidence.resolve();out=a.out.resolve()
    if any(p.is_relative_to(ROOT) for p in (evidence,out)) or out.exists() or out.is_relative_to(evidence):raise SystemExit("Use fresh off-Git controls outside source evidence")
    assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()==BASE,"Use exact frozen overlay"
    with LOCK.open("a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX);out.mkdir(parents=True);results=[]
        for name in ("positive","whole-law-witness-missing","whole-law-axiom-log-corrupt"):
            case=out/name
            shutil.copytree(evidence,case,copy_function=lambda src,dst:os.symlink(src,dst))
            for output in ("verified-census.json","uncovered.json"):
                p=case/output
                if p.exists():p.unlink()
            if name=="whole-law-axiom-log-corrupt":
                meta_path=case/"serial/olean/tests/h62/item2/audit-theories/LeafProgressWitnesses.audit-result.json"
                meta=json.loads(meta_path.read_text());lines=Path(meta["log"]).read_text().splitlines();prefix="'H62.AuditTheories.leaf_builtin_inputs_joint' "
                assert sum(line.startswith(prefix) for line in lines)==1
                altered="\n".join(prefix+"depends on axioms: [sorryAx]" if line.startswith(prefix) else line for line in lines)+"\n"
                log=case/"tampered-whole-law-axioms.log";log.write_text(altered)
                meta["log"]=str(log);meta["log_sha256"]=hashlib.sha256(log.read_bytes()).hexdigest();meta_path.unlink();meta_path.write_text(json.dumps(meta,indent=2)+"\n")
            args=["--evidence",str(case),"--require-complete-explicit-module",MODULE]
            code="import sys;sys.path.insert(0,"+repr(str(ROOT/"scripts/h62/item2/audit-theories"))+");import verify_census as v;"
            if name=="whole-law-witness-missing":code+="v.WITNESSES.pop("+repr(REQUIRED)+");"
            code+="sys.argv=['verify_census.py']+"+repr(args)+";v.main()"
            command=[sys.executable,"-c",code];run=subprocess.run(command,cwd=ROOT,env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1"),capture_output=True,text=True)
            (case/"control.log").write_text(run.stdout+run.stderr)
            if name=="positive":assert run.returncode==0 and "EXPLICIT_MODULE_PASS:" in run.stdout,run.stdout+run.stderr
            elif name=="whole-law-witness-missing":
                assert run.returncode==1 and "EXPLICIT_MODULE_BLOCKED:" in run.stdout and "1 pending explicit" in run.stdout,run.stdout+run.stderr
                row=next(r for r in json.loads((case/"verified-census.json").read_text())["declarations"] if r["source_name"]==REQUIRED)
                assert row["status"]=="uncovered" and "certificate" not in row
            else:assert run.returncode==1 and "AssertionError" in run.stderr,run.stdout+run.stderr
            results.append(dict(case=name,command=command,cwd=str(ROOT),exit=run.returncode,accepted=name=="positive"))
        (out/"controls.json").write_text(json.dumps(dict(cases=results,lean_jobs=0,full_assignment_acceptance=False),indent=2)+"\n")
    print("LEAF_PROGRESS_CONTROLS_PASS:complete6;missing_whole_law_packet_refused;forbidden_axiom_refused")
if __name__=="__main__":main()
