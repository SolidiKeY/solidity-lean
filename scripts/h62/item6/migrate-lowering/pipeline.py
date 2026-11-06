#!/usr/bin/env python3
"""Continue an already-running clean old gate, then one clean pinned new gate."""
import fcntl, hashlib, json, os, subprocess, time
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
env=dict(os.environ,PATH=str(config/"bin")+":"+str(toolchain/"bin")+":"+os.environ["PATH"],XDG_CACHE_HOME=str(artifacts/"new-cache"),LEAN_NUM_THREADS="1",SOLKEY_RULES="/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key")
new=evidence/"new-clean-full.json"
rc=subprocess.run(["python3",str(script/"bounded.py"),"--output",str(new),"--lock-fd",str(lock.fileno()),"--","./run-lean.sh"],env=env,pass_fds=(lock.fileno(),)).returncode
lock.close()
if not new.exists(): raise SystemExit("new gate setup failed; inspect pipeline driver log")
b=json.loads(new.read_text()); delta=(b["wall_seconds"]/a["wall_seconds"]-1)*100 if not rc else None
rss_delta=(b["sampled_peak_group_rss_bytes"]/a["sampled_peak_group_rss_bytes"]-1)*100 if not rc and a["sampled_peak_group_rss_bytes"] else None
regression=max(delta,rss_delta) if delta is not None and rss_delta is not None else None
status="blocked" if rc or regression is None or regression>0 else "validation-pending"
blocker="NEW_GATE_FAILED" if rc else "MISSING_COMPARISON_METRIC" if regression is None else "SLOWDOWN_GT_10_PERCENT_STOP" if regression is not None and regression>10 else "REGRESSION_ESCALATION" if regression is not None and regression>0 else None
result.write_text(json.dumps({"status":status,"blocker":blocker,"old":a,"new":b,"wall_delta_percent":delta,"sampled_rss_delta_percent":rss_delta,"note":"No migration completion: assigned module acceptance, type/axiom checks, owner coordination and milestone reviews still required."},indent=2)+"\n")
print(result.read_text(),flush=True)
raise SystemExit(1 if blocker else 0)
