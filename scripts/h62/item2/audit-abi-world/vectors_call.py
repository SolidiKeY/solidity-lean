#!/usr/bin/env python3
"""Bind vector diagnostics to every local audit Lean source before/after."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
root=Path(__file__).resolve().parents[4]
folder=root/"tests/h62/item2/audit-abi-world/H62AbiWorld"
def dependencies():
 return {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(folder.glob("*.lean"))}
before=dependencies()
params=json.dumps(dict(file_path=str((folder/"RuntimeVectors.lean").relative_to(root)),interactive=False,timeout_s=240))
result=subprocess.run([str(root/".venv/bin/python"),"-B",str(Path(__file__).with_name("mcp_call.py")),"lean_diagnostic_messages",params],cwd=root,stdout=subprocess.PIPE,text=True)
report=json.loads(result.stdout)
report["_vector_dependencies"]={"before":before,"after":dependencies()}
print(json.dumps(report))
assert before==dependencies(),"audit dependencies changed during fidelity check"
raise SystemExit(result.returncode)
