#!/usr/bin/env python3
"""Continue an already-running clean old gate, then one clean pinned new gate."""
import fcntl, hashlib, json, math, os, subprocess, time
from pathlib import Path
root=Path.cwd(); artifacts=Path("/workspace/migrate-lowering-artifacts"); evidence=artifacts/"evidence"
old=evidence/"old-clean-full.json"; result=evidence/"pipeline.json"
while not old.exists(): time.sleep(10)
lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a")
fcntl.flock(lock,fcntl.LOCK_EX)
a=json.loads(old.read_text())
if a["cwd"]!=str(root) or a["command"]!=["./run-lean.sh"]: raise SystemExit("unexpected old gate provenance")
subprocess.run(["git","diff","--exit-code","c6f550e281a7e5affa9a99bc2cdaed556dec00e4","--","Solidity","lakefile.toml","lean-toolchain","run-lean.sh"],check=True)
if a["exit"] or a["stop_reason"]:
    result.write_text(json.dumps({"status":"blocked","blocker":"OLD_BASELINE_GATE_FAILED","old":a},indent=2)+"\n"); raise SystemExit(1)
# Coordinator requires a fresh master/code check before a new item.
subprocess.run(["git","fetch","origin","master"],check=True)
master=subprocess.check_output(["git","rev-parse","origin/master"],text=True).strip()
recent=subprocess.check_output(["git","log","-12","--oneline","origin/master"],text=True)
changed=subprocess.check_output(["git","diff","--name-only","c6f550e281a7e5affa9a99bc2cdaed556dec00e4..origin/master","--","Solidity/Lowering"],text=True).splitlines()
master_toolchain=subprocess.check_output(["git","show","origin/master:lean-toolchain"],text=True).strip()
check={"master":master,"recent_log":recent,"owned_paths_changed":changed,"toolchain":master_toolchain}
(evidence/"master-pre-new.json").write_text(json.dumps(check,indent=2)+"\n")
if changed or master_toolchain!="leanprover/lean4:v4.24.0":
    result.write_text(json.dumps({"status":"blocked","blocker":"MASTER_MIGRATION_LANDED_REBASE_REVIEW","master_check":check,"note":"Review/rebase already-landed work before starting the new item; preserve this pinned baseline and redo matched measurements if inputs change."},indent=2)+"\n")
    raise SystemExit(1)
pin=json.loads(Path("/workspace/h62-coordinator-inputs/toolchain-pin.json").read_text())
archive=artifacts/"toolchains"/pin["asset"]
if hashlib.sha256(archive.read_bytes()).hexdigest()!=pin["sha256"]: raise SystemExit("pinned archive mismatch")
# Preserve the old build, then start with no new-toolchain build artifacts.
build=root/".lake/build"; saved=artifacts/"old-build"
if saved.exists(): raise SystemExit("refusing to overwrite old build")
print(subprocess.check_output(["git","status","--short"],text=True),flush=True)
build.rename(saved)
toolchain=artifacts/"toolchains/lean-4.35.0-linux"; config=artifacts/"new-config"
script=root/"scripts/h62/item6/migrate-lowering"
subprocess.run(["python3",str(script/"prepare_config.py"),"--toolchain",str(toolchain),"--output",str(config)],check=True)
env=dict(os.environ,PATH=str(config/"bin")+":"+str(toolchain/"bin")+":"+os.environ["PATH"],XDG_CACHE_HOME=str(artifacts/"new-cache"),LEAN_NUM_THREADS="1",MIGRATION_LAKE_CONFIG=str(config/"lakefile.toml"),SOLKEY_RULES="/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key")
new=evidence/"new-clean-full.json"
rc=subprocess.run(["python3",str(script/"bounded.py"),"--output",str(new),"--lock-fd",str(lock.fileno()),"--","./run-lean.sh"],env=env,pass_fds=(lock.fileno(),)).returncode
lock.close()
if not new.exists(): raise SystemExit("new gate setup failed; inspect pipeline driver log")
b=json.loads(new.read_text())
gate_failed=bool(rc or b.get("exit")!=0 or b.get("stop_reason"))
settings_match=all(k in a and k in b and a[k]==b[k] for k in ("cgroup_cap_bytes","reserve_bytes","LEAN_NUM_THREADS","sample_interval_seconds","memory_policy","guard_sha256","config_sha256","cpu_max","cpuset_cpus_effective","affinity_cpus"))
settings_match=settings_match and all(isinstance(m.get(k),str) and len(m[k])==64 for m in (a,b) for k in ("guard_sha256","config_sha256"))
valid=settings_match and all(isinstance(m.get(k),(int,float)) and math.isfinite(m[k]) and m[k]>0 for m in (a,b) for k in ("wall_seconds","sampled_peak_group_rss_bytes"))
delta=(b["wall_seconds"]/a["wall_seconds"]-1)*100 if not gate_failed and valid else None
rss_delta=(b["sampled_peak_group_rss_bytes"]/a["sampled_peak_group_rss_bytes"]-1)*100 if not gate_failed and valid else None
regression=max(delta,rss_delta) if delta is not None and rss_delta is not None else None
status="blocked" if gate_failed or regression is None or regression>0 else "validation-pending"
blocker="NEW_GATE_FAILED" if gate_failed else "RESOURCE_SETTINGS_MISMATCH" if not settings_match else "MISSING_COMPARISON_METRIC" if regression is None else "SLOWDOWN_GT_10_PERCENT_STOP" if regression>10 else "REGRESSION_ESCALATION" if regression>0 else None
result.write_text(json.dumps({"status":status,"blocker":blocker,"old":a,"new":b,"wall_delta_percent":delta,"sampled_rss_delta_percent":rss_delta,"note":"No migration completion: assigned module acceptance, type/axiom checks, owner coordination and milestone reviews still required."},indent=2)+"\n")
subprocess.run(["python3",str(script/"acceptance.py")],check=True)
print(result.read_text(),flush=True)
raise SystemExit(1 if blocker else 0)
