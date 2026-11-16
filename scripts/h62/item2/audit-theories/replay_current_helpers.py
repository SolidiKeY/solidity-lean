#!/usr/bin/env python3
"""Fresh bounded replay of every current audit helper; historical census stays separate.
No full integration, migration, compiler-branch or whole-tree equivalence claim.
"""
import argparse,fcntl,hashlib,json,os,subprocess,sys
from pathlib import Path
from census import ROOT
from run_frozen_history import LOCK

def helper_targets(root):
    return sorted(str(p.relative_to(root)) for p in (root/"tests/h62/item2/audit-theories").rglob("*.lean") if p.name!="ElaboratedCensus.lean")

def require_complete_targets(targets,helpers):
    sources=[row["source"] for row in helpers["modules"]]
    assert len(sources)==len(set(sources)) and set(sources)==set(targets),"Verified helper census differs from recursive replay targets"

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ("lean","cache","out"):ap.add_argument("--"+name,type=Path,required=True)
    a=ap.parse_args();lean=a.lean.resolve();cache=a.cache.resolve();out=a.out.resolve()
    if cache.is_relative_to(ROOT) or out.is_relative_to(ROOT) or out.exists() or out.is_relative_to(cache):raise SystemExit("Use fresh off-Git output outside cache")
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1");rows=[]
    with LOCK.open("a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX);out.mkdir(parents=True);(out/"serial").symlink_to(cache,target_is_directory=True)
        targets=helper_targets(ROOT);assert len(targets)==20
        head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()
        sources={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in targets}
        (out/"setup.json").write_text(json.dumps(dict(source_head=head,repository=str(ROOT),helper_sources=sources,driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),indent=2)+"\n")
    def run(name,command):
        command=[str(x) for x in command];log=out/(name+".log")
        with log.open("w") as stream:p=subprocess.run(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        rows.append(dict(command=command,cwd=str(ROOT),exit=p.returncode,log=str(log)));(out/"current-gates.json").write_text(json.dumps(rows,indent=2)+"\n");p.check_returncode()
    run("serial",[sys.executable,Path(__file__).with_name("serial_check.py"),"--lean",lean,"--out",cache,"--fresh-targets","Solidity/KeySort.lean",*targets])
    with LOCK.open("a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()==head
        assert sources=={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in targets}
        run("verify_helpers",[sys.executable,Path(__file__).with_name("verify_helpers.py"),"--evidence",out])
        run("verify_totality",[sys.executable,Path(__file__).with_name("verify_totality.py"),"--evidence",out])
        checks=json.loads((cache/"results.json").read_text())["checks"];by_name={x["module"]:x for x in checks}
        wanted=["Solidity.KeySort",*[p[:-5].replace("/",".") for p in targets]]
        assert all(not by_name[n].get("cache_hit") and by_name[n]["exit"]==0 and by_name[n]["resource_stop"] is None for n in wanted)
        helpers=json.loads((out/"verified-helpers.json").read_text());require_complete_targets(targets,helpers);assert helpers["proved_theorems"]==198 and helpers["fixture_predicate_definitions"]==51 and helpers["private_type_abbreviations"]==7
        summary=dict(source_head=head,helper_modules=20,fresh_helper_theorems=198,fixture_definitions=51,private_abbreviations=7,fresh_KeySort=by_name["Solidity.KeySort"],all_requested_targets_fresh=True,full_assignment_acceptance=False,boundary="All current audit helper proof modules and KeySort freshly checked. Original theorem accounting remains historical; no whole-tree equivalence, full integration, migration or new physical compiler coverage.")
        (out/"current-summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    print("CURRENT_HELPER_REPLAY_PASS:20freshmodules;198theorems;freshKeySort;full_acceptance=false")
if __name__=="__main__":main()
