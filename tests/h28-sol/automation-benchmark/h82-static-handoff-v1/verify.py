"""Static packet checks only; does not execute Lean or apply the proposal."""
from pathlib import Path
import hashlib
import json
import subprocess

packet = Path(__file__).resolve().parent
repo = packet.parents[3]
entries = json.loads((packet / "evidence-manifest.json").read_text())
for entry in entries:
    source = Path(entry["path"])
    assert source.stat().st_size == entry["bytes"], source
    assert hashlib.sha256(source.read_bytes()).hexdigest() == entry["sha256"], source
assert len(entries) == 20
state = json.loads((packet / "reconciliation.json").read_text())
assert not state["runtime_gate_pass"]
assert not state["audit_calculus"]["merged"]
for name in ["tests/h28-sol/automation-benchmark/ContextControls.lean",
             "Solidity/Automation/H28/Context.lean", "lean-toolchain"]:
    committed = subprocess.check_output(["git", "show", "HEAD:" + name], cwd=repo)
    assert committed == (repo / name).read_bytes(), name
subprocess.run(["git", "apply", "--check", str(packet / "API-only.unvalidated.patch")],
               cwd=repo, check=True)
print("PASS: 20 source/receipt hashes; live sources and pin unchanged; patch dry-run only")
print("No Lean execution or formal/runtime/trust acceptance")
