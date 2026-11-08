#!/usr/bin/env python3
"""Rebuild lost frozen audit receipts from committed sources, without a prior cache.
Original sources remain untouched; overlay only the assigned additive audit scope.
Uses serial_check resource limits and mandatory KeySort. Not a final runtime gate.
"""
import argparse,fcntl,hashlib,io,json,os,shutil,subprocess,sys,tarfile
from pathlib import Path
from census import ROOT,BASE
from run_frozen_history import SCOPE,LOCK

def digest(path):
    with path.open("rb") as stream:return hashlib.file_digest(stream,"sha256").hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ("checkout","evidence","lean"):ap.add_argument("--"+name,type=Path,required=True)
    a=ap.parse_args();checkout=a.checkout.resolve();out=a.evidence.resolve();lean=a.lean.resolve()
    if any(p.is_relative_to(ROOT) for p in (checkout,out)):raise SystemExit("Use off-Git paths")
    if checkout.exists() or out.exists():raise SystemExit("Refuse to overwrite checkout or evidence")
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1");gates=[]
    def save(name,obj):(out/name).write_text(json.dumps(obj,indent=2)+"\n")
    def run(cmd,name,extra=None):
        with (out/name).open("w") as log:
            result=subprocess.run([str(x) for x in cmd],cwd=checkout,env=env| (extra or {}),stdout=log,stderr=subprocess.STDOUT)
        gates.append(dict(command=[str(x) for x in cmd],cwd=str(checkout),exit=result.returncode,log=str(out/name)))
        save("gates.json",gates);result.check_returncode()
    LOCK.parent.mkdir(parents=True,exist_ok=True)
    with LOCK.open("a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        if subprocess.check_output(["git","status","--porcelain"],cwd=ROOT):raise SystemExit("Commit the audit tools before rebuilding")
        head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()
        subprocess.run(["git","merge-base","--is-ancestor",BASE,head],cwd=ROOT,check=True)
        out.mkdir(parents=True)
        subprocess.run(["git","worktree","add","--detach",str(checkout),BASE],cwd=ROOT,check=True)
        payload=subprocess.check_output(["git","archive",head,"--",*SCOPE],cwd=ROOT)
        (out/"audit-overlay.tar").write_bytes(payload)
        with tarfile.open(fileobj=io.BytesIO(payload)) as tar:
            for member in tar:
                name=member.name.rstrip("/")
                assert not Path(name).is_absolute() and ".." not in Path(name).parts
                assert any(name==s or name.startswith(s+"/") or member.isdir() and s.startswith(name+"/") for s in SCOPE),name
                target=checkout/name
                if member.isdir():target.mkdir(parents=True,exist_ok=True)
                else:
                    assert member.isfile(),name
                    target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(tar.extractfile(member).read())
        run(["git","diff","--exit-code"],"frozen-tracked-clean-before.log")
        pin=(checkout/"lean-toolchain").read_text().strip().rsplit(":v",1)[1]
        version=subprocess.check_output([str(lean),"--version"],text=True).strip()
        assert "version "+pin+"," in version,(pin,version)
        save("setup.json",dict(frozen_base=BASE,overlay_head=head,overlay_sha256=digest(out/"audit-overlay.tar"),scope=SCOPE,lean_version=version,checkout=str(checkout),full_assignment_acceptance=False))
    tool=checkout/"scripts/h62/item2/audit-theories"
    targets=sorted(str(p.relative_to(checkout)) for p in (checkout/"tests/h62/item2/audit-theories").glob("*.lean"))
    run([sys.executable,tool/"serial_check.py","--lean",lean,"--out",out/"serial",*targets],"serial-driver.log",{"H62_AUDIT_CENSUS_OUT":str(out/"elaborated.json")})
    with LOCK.open("a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        shutil.copyfile(out/"serial/results.json",out/"serial/baseline-results.json")
    run([sys.executable,tool/"serial_check.py","--lean",lean,"--out",out/"serial","tests/h62/item2/audit-theories/ElaboratedCensus.lean"],"replay-driver.log",{"H62_AUDIT_CENSUS_OUT":str(out/"elaborated-replay.json")})
    with LOCK.open("a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        data=out/"elaborated.json";assert data.read_bytes()==(out/"elaborated-replay.json").read_bytes(),"Non-deterministic typed census"
        meta=json.loads((out/"serial/olean/tests/h62/item2/audit-theories/ElaboratedCensus.audit-result.json").read_text())
        save("census-output-receipt.json",dict(producer_exit=meta["exit"],sha256=digest(data),bytes=data.stat().st_size,**{"producer_"+k:meta[k] for k in ("source_transitive_sha256","olean_sha256","log_sha256")}))
        save("census-replay.json",dict(sha256=digest(data),bytes=data.stat().st_size,identical=True))
        run([sys.executable,tool/"census.py","--out",out/"census"],"source-census.log")
        run([sys.executable,tool/"verify_census.py","--evidence",out],"verified-census.log")
        run([sys.executable,tool/"verify_helpers.py","--evidence",out],"verified-helpers.log")
        run([sys.executable,tool/"verify_totality.py","--evidence",out],"verified-totality.log")
        run(["git","diff","--exit-code"],"frozen-tracked-clean-after.log")
        files=sorted(p for p in out.rglob("*") if p.is_file() and p.name!="SHA256SUMS")
        (out/"SHA256SUMS").write_text("".join(digest(p)+"  "+str(p.relative_to(out))+"\n" for p in files))
    print("FROZEN_EVIDENCE_REBUILD_PASS; no new coverage or RUNTIME_GATE_PASS")

if __name__=="__main__":main()
