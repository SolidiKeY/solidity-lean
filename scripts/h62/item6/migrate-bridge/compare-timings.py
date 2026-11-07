#!/usr/bin/env python3
"""Compare completed bounded timings; this never certifies proof/full-gate acceptance."""
import argparse, decimal, fractions, json, pathlib, re
PROFILE=("command","measurement_scope","build_tree_policy","compiler_args","module_timeout_seconds","reserve_gib","swap_bytes","cache","solkey_rules_sha256")
class Blocked(ValueError): pass

def load_run(directory, version):
    try:
        receipt=json.loads((directory/"receipt.json").read_text())
        if not isinstance(receipt,dict): raise Blocked("receipt must be an object")
        if "resource_stop" not in receipt: raise Blocked("missing resource-stop evidence")
        if receipt.get("status")!="command-pass" or type(receipt.get("exit")) is not int or receipt["exit"]!=0 or receipt["resource_stop"] is not None:
            raise Blocked("run did not complete successfully: "+str(directory))
        if any(k not in receipt for k in PROFILE): raise Blocked("missing resource/cache profile")
        if receipt["command"] not in (["bash","./run-lean.sh","--bridge"],["bash","./scripts/check-bridge.sh"]): raise Blocked("unsupported measurement command")
        scope="Bridge" if receipt["command"]==["bash","./scripts/check-bridge.sh"] else "full-root-and-Bridge"
        expected={"measurement_scope":scope,"build_tree_policy":"Lean library outputs cold; prebuilt ProofWidgets JS only","compiler_args":["-j1","-M10240"],"module_timeout_seconds":300,"reserve_gib":4,"swap_bytes":0,"cache":"disabled via empty LAKE_CACHE_DIR and --no-cache"}
        if any(type(receipt[k]) is not type(v) or receipt[k]!=v for k,v in expected.items()): raise Blocked("invalid bounded-run profile")
        if not isinstance(receipt["solkey_rules_sha256"],str) or not re.fullmatch("[0-9a-f]{64}",receipt["solkey_rules_sha256"]): raise Blocked("invalid rules-input hash")
        if not isinstance(receipt.get("versions"),dict): raise Blocked("missing versions")
        versions=receipt["versions"]
        if not all(isinstance(versions.get(k),str) for k in ("lean","lake")): raise Blocked("missing version strings")
        if "version "+version+"," not in versions.get("lean","") or "(Lean version "+version+")" not in versions.get("lake",""):
            raise Blocked("unexpected Lean/Lake version: "+str(directory))
        value=receipt.get("elapsed_seconds")
        if isinstance(value,bool): raise Blocked("invalid elapsed time")
        elapsed=decimal.Decimal(str(value))
        if not elapsed.is_finite() or elapsed<=0: raise Blocked("invalid elapsed time")
        # The first active baseline used a separate VM-headroom watchdog.
        if (directory/"active-attempt-runner.py").exists():
            watchdog=json.loads((directory/"cgroup-watchdog.json").read_text())
            required=("resource_stop","reserve_gib","elapsed_seconds","watched_pgid","peak_vm_cgroup_bytes")
            if not isinstance(watchdog,dict) or any(k not in watchdog for k in required): raise Blocked("watchdog completion evidence incomplete")
            if watchdog["resource_stop"] is not None or type(watchdog["reserve_gib"]) is not int or watchdog["reserve_gib"]!=4: raise Blocked("watchdog failed or has invalid reserve")
            if type(watchdog["watched_pgid"]) is not int or watchdog["watched_pgid"]<=0 or type(watchdog["peak_vm_cgroup_bytes"]) is not int or watchdog["peak_vm_cgroup_bytes"]<0: raise Blocked("invalid watchdog process/resource evidence")
            watchdog_elapsed=decimal.Decimal(str(watchdog["elapsed_seconds"]))
            if isinstance(watchdog["elapsed_seconds"],bool) or not watchdog_elapsed.is_finite() or watchdog_elapsed<=0: raise Blocked("invalid watchdog elapsed time")
        return receipt,elapsed
    except (OSError,KeyError,TypeError,decimal.InvalidOperation,json.JSONDecodeError) as error:
        raise Blocked("incomplete or malformed run: "+str(directory)+": "+str(error)) from error

def compare(old_dir,new_dir):
    old,old_time=load_run(old_dir,"4.24.0"); new,new_time=load_run(new_dir,"4.35.0")
    if any(old[k]!=new[k] for k in PROFILE): raise Blocked("resource, command, rules input or cache profiles differ")
    ratio=fractions.Fraction(new_time)/fractions.Fraction(old_time)
    delta=(new_time/old_time-1)*100
    action="stop" if ratio>fractions.Fraction(11,10) else "escalate" if ratio>1 else "no-regression"
    return {"schema":1,"measurement_scope":old["measurement_scope"],"command":old["command"],"old_seconds":str(old_time),"new_seconds":str(new_time),"delta_percent":str(delta),"delta_percent_exact_fraction":str((ratio-1)*100),"action":action,
            "proof_and_full_gate_acceptance":"not assessed; independent acceptance remains required",
            "old_versions":old["versions"],"new_versions":new["versions"]}

def main():
    ap=argparse.ArgumentParser(description=__doc__); ap.add_argument("--old",type=pathlib.Path,required=True); ap.add_argument("--new",type=pathlib.Path,required=True); args=ap.parse_args()
    try: result=compare(args.old,args.new)
    except Blocked as error:
        print(json.dumps({"schema":1,"action":"blocked","reason":str(error)},sort_keys=True)); return 2
    print(json.dumps(result,indent=2,sort_keys=True))
    return {"no-regression":0,"escalate":3,"stop":4}[result["action"]]
if __name__=="__main__": raise SystemExit(main())
