#!/usr/bin/env python3
"""Run unchanged repository source gates; no shared registrations are rewritten."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time
root=Path(__file__).resolve().parents[2]
os.chdir(root)
os.environ["PATH"]=str(Path(sys.executable).resolve().parent)+os.pathsep+os.environ["PATH"]
os.environ["SOLKEY_EXAMPLES"]=str(root/"tests/migration/solkey/keyext.solidity.examples")
commands=[
 ["bash","scripts/check-trust.sh"],
 ["node","scripts/check-orphans.mjs"],
 ["node","scripts/check-layers.mjs"],
 ["bash","scripts/coord-tools/register.sh","--check"],
 ["bash","scripts/check-doc-paths.sh"],
 ["node","scripts/check-axiom-pins.mjs"],
 ["bash","scripts/check-testsuite.sh"],
 ["node","scripts/check-automatic.mjs","--strict"],
]
rows=[]
for i,cmd in enumerate(commands):
 p=root/"tests/sol-c3-exactness/evidence"/f"final-source-{i+1}.log"
 start=time.monotonic()
 with p.open("w") as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
 row={"command":cmd,"exit":r.returncode,"elapsed_seconds":time.monotonic()-start,"log":str(p.relative_to(root)),"log_sha256":hashlib.sha256(p.read_bytes()).hexdigest()};rows.append(row)
 print(("PASS " if r.returncode==0 else "FAIL ")+" ".join(cmd),flush=True)
p=root/"tests/sol-c3-exactness/evidence/final-source-gates.json"
p.write_text(json.dumps(rows,indent=2)+"\n")
print("SOURCE_GATE_PACKET_SHA256 "+hashlib.sha256(p.read_bytes()).hexdigest(),flush=True)
sys.exit(int(any(r["exit"]!=0 for r in rows)))
