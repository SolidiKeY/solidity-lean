#!/usr/bin/env python3
"""Check additive audit helpers against the exact original frozen Git tree.
Creates a detached validation worktree, overlays ONLY committed assigned audit
paths, and uses bounded serial Lean. No original source edits/versioned pairs,
no new lane branch/goal, no publication. Keep resulting worktree and evidence.
"""
import argparse,fcntl,hashlib,io,json,os,subprocess,tarfile
from pathlib import Path
from census import ROOT,BASE
SCOPE=["tests/h62/item2/audit-theories","scripts/h62/item2/audit-theories","docs/feature-work/h62-2-audit-theories.md"]
LOCK=Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for n in("checkout","evidence","lean","cache","historical-evidence"):ap.add_argument("--"+n,type=Path,required=True)
    ap.add_argument("--source-head",required=True);a=ap.parse_args();checkout=a.checkout.resolve();out=a.evidence.resolve();cache=a.cache.resolve();old=a.historical_evidence.resolve();lean=a.lean.resolve()
    if any(p.is_relative_to(ROOT)for p in(checkout,out,cache,old)):raise SystemExit("Use off-Git validation/evidence paths")
    out.mkdir(parents=True,exist_ok=True);env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1");rows=[]
    def run(cmd,cwd,logname):
        log=out/logname
        with log.open("w")as stream:x=subprocess.run(cmd,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
        rows.append(dict(command=[str(x)for x in cmd],cwd=str(cwd),exit=x.returncode,log=str(log)))
        (out/"history-gates.json").write_text(json.dumps(rows,indent=2)+"\n");x.check_returncode();return log
    with LOCK.open("a")as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        assert not checkout.exists(),"Refuse to overwrite an existing validation checkout"
        source_head=subprocess.check_output(["git","rev-parse",a.source_head+"^{commit}"],cwd=ROOT,text=True).strip()
        subprocess.run(["git","merge-base","--is-ancestor",source_head,"HEAD"],cwd=ROOT,check=True)
        run(["git","worktree","add","--detach",str(checkout),BASE],ROOT,"worktree-create.log")
        payload=subprocess.check_output(["git","archive","--format=tar",source_head,"--",*SCOPE],cwd=ROOT);archive=out/"audit-overlay.tar";archive.write_bytes(payload)
        with tarfile.open(fileobj=io.BytesIO(payload))as tar:
            for member in tar:
                name=member.name.rstrip("/");parts=Path(name).parts
                assert not Path(name).is_absolute()and".."not in parts
                inside=any(name==s or name.startswith(s+"/")for s in SCOPE)
                parent=member.isdir()and any(s.startswith(name+"/")for s in SCOPE)
                assert inside or parent,name
                target=checkout/name
                if member.isdir():target.mkdir(parents=True,exist_ok=True)
                else:
                    assert member.isfile(),name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(tar.extractfile(member).read())
        run(["git","diff","--exit-code"],checkout,"original-tracked-clean-before.log")
        assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=checkout,text=True).strip()==BASE
        setup={"frozen_commit":BASE,"frozen_tree":subprocess.check_output(["git","rev-parse",BASE+"^{tree}"],cwd=ROOT,text=True).strip(),"audit_overlay_source_head":source_head,"audit_overlay_archive_sha256":sha(archive),"source_repository":str(ROOT),"frozen_checkout":str(checkout),"scope":SCOPE,"driver_sha256":sha(Path(__file__).resolve()),"boundary":"Detached original-history validation only; additive audit overlay. No original tracked source changes or auditor-created versioned pairs."}
        (out/"history-setup.json").write_text(json.dumps(setup,indent=2)+"\n")
        assert not(out/"serial").exists();run(["cp","-a","--reflink=auto",str(cache),str(out/"serial")],ROOT,"cache-copy.log")
    tool=checkout/"scripts/h62/item2/audit-theories";targets=sorted(str(p.relative_to(checkout))for p in(checkout/"tests/h62/item2/audit-theories").glob("*.lean")if p.name!="ElaboratedCensus.lean")
    run(["python3",str(tool/"serial_check.py"),"--lean",str(lean),"--out",str(out/"serial"),"--fresh-targets","Solidity/KeySort.lean",*targets],checkout,"original-serial-driver.log")
    with LOCK.open("a")as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        commands=[(["python3",str(tool/"census.py"),"--out",str(out/"census")],"original-census.log"),(["python3",str(tool/"verify_helpers.py"),"--evidence",str(out)],"original-helpers.log"),(["python3",str(tool/"coverage_ledger.py"),"--out",str(out),"--proof-evidence",str(out),"--historical-evidence",str(old)],"original-ledger.log"),(["python3",str(tool/"pure_input_roles.py"),"--out",str(out),"--proof-evidence",str(out),"--historical-evidence",str(old)],"original-roles.log"),(["python3",str(tool/"verify_acceptance_snapshot.py"),"--evidence",str(out),"--roles",str(out/"all-reviewed-pure-input-roles.json"),"--historical-evidence",str(old),"--out",str(out)],"original-snapshot.log"),(["python3",str(tool/"verify_payable.py"),"--evidence",str(out),"--require-ordinary-complete"],"original-payable.log"),(["python3",str(tool/"verify_totality.py"),"--evidence",str(out)],"original-totality.log"),(["git","diff","--exit-code"],"original-tracked-clean-after.log")]
        for cmd,name in commands:run(cmd,checkout,name)
        dirty=subprocess.check_output(["git","status","--porcelain=v1","--untracked-files=all"],cwd=checkout,text=True).splitlines()
        assert all(line.startswith("?? ")and any(line[3:]==s or line[3:].startswith(s+"/")for s in SCOPE)for line in dirty)
        helpers=json.loads((out/"verified-helpers.json").read_text());snapshot=json.loads((out/"acceptance-snapshot.json").read_text());census=json.loads((out/"census/census.json").read_text())
        assert snapshot["current_head"]==BASE and not snapshot["changed_frozen_files"]and not snapshot["mapped_file_fidelity_changes"]
        assert census["counts"]["modules"]==25 and census["counts"]["theorems"]==500
        result={**setup,"original_tracked_sources_unchanged":True,"original_census_modules":25,"original_explicit_declarations":500,"checked_original_helper_theorems":helpers["proved_theorems"],"original_joint_certificates":snapshot["joint_certificates"],"accepted_original_H69":snapshot["accepted_H69"],"original_remaining_records":snapshot["remaining_original_records"],"fidelity_question":"Q-FROZEN-REBASE resolved by checked original-history audit; current rebased coverage separate, no equivalence claim.","full_assignment_acceptance":False,"gate_manifest_sha256":sha(out/"history-gates.json")}
        (out/"frozen-history-audit.json").write_text(json.dumps(result,indent=2)+"\n")
    print("FROZEN_HISTORY_AUDIT_PASS "+json.dumps(result))
if __name__=="__main__":main()
