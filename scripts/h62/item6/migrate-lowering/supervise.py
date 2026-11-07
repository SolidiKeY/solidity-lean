#!/usr/bin/env python3
"""Detached supervisor: bounded clean old gate, then the serial pinned pipeline."""
import json, os, subprocess
from process_group import stop_owned
from datetime import datetime, timezone
from pathlib import Path
root=Path.cwd(); artifacts=Path("/workspace/migrate-lowering-artifacts"); evidence=artifacts/"evidence"
script=root/"scripts/h62/item6/migrate-lowering"
state=evidence/"supervisor.json"
def save(status,**fields):
    obj=dict(status=status,supervisor_pid=os.getpid(),timestamp_utc=datetime.now(timezone.utc).isoformat(),**fields)
    tmp=state.with_suffix(".tmp"); tmp.write_text(json.dumps(obj,indent=2)+"\n"); tmp.replace(state)
def cleanup_owned(livefile,runner_pid=None):
    if not livefile.exists(): return
    live=json.loads(livefile.read_text())
    if runner_pid is not None and live.get("runner_pid")!=runner_pid: return
    if live.get("status")!="running": return
    stop_owned(live["process_group"],root)
if (evidence/"old-clean-full.json").exists() or (evidence/"new-clean-full.json").exists():
    raise SystemExit("refusing to overwrite an existing gate result")
if (root/".lake/build").exists(): raise SystemExit("old baseline must start with absent .lake/build")
env=dict(os.environ,PATH=str(artifacts/"old-config/bin")+":/workspace/.setup/tools/lean-4.24.0-linux/bin:"+os.environ["PATH"],XDG_CACHE_HOME=str(artifacts/"old-cache"),LEAN_NUM_THREADS="1",MIGRATION_LAKE_CONFIG=str(artifacts/"old-config/lakefile.toml"),SOLKEY_RULES="/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key")
save("old-gate-starting")
old=subprocess.Popen(["python3",str(script/"bounded.py"),"--output",str(evidence/"old-clean-full.json"),"--","./run-lean.sh"],env=env)
save("old-gate-running",runner_pid=old.pid)
rc=old.wait()
if rc:
    cleanup_owned(evidence/"old-clean-full.live.json",old.pid)
    save("blocked",blocker="OLD_BASELINE_GATE_FAILED",exit=rc); raise SystemExit(rc)
save("new-pipeline-starting")
rc=subprocess.run(["python3",str(script/"pipeline.py")]).returncode
if rc: cleanup_owned(evidence/"new-clean-full.live.json")
save("blocked" if rc else "validation-pending",pipeline_exit=rc)
raise SystemExit(rc)
