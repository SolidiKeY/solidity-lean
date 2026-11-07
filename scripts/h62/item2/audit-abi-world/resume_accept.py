#!/usr/bin/env python3
"""Read-only post-merge acceptance; original frozen receipts stay immutable.

Current encode output must equal the archived external fixtures byte for byte.
This reuses external observations for identical inputs; it does not turn them
into Lean gas/fork proofs or claim another reference execution.
"""
import argparse,hashlib,json,re,subprocess
from pathlib import Path
from prepare_resume_config import INTEGRATION
import census
from resume_sources import snapshot
root=Path(__file__).resolve().parents[4]
p=argparse.ArgumentParser();p.add_argument("--evidence",type=Path,required=True);p.add_argument("--frozen-evidence",type=Path);args=p.parse_args();e=args.evidence
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
folder=root/"tests/h62/item2/audit-abi-world/H62AbiWorld"
local={str(p.relative_to(root)):sha(p) for p in sorted(folder.glob("*.lean"))}
assert len(local)==9
upstream=snapshot()
assert not subprocess.check_output(["git","diff","--name-only",INTEGRATION,"--","Solidity","lakefile.toml","lean-toolchain"],cwd=root).strip()
for path in [census.MAP]+census.module_paths(census.frozen(census.MAP)):
 assert (root/path).read_bytes()==subprocess.check_output(["git","show",census.BASE+":"+path],cwd=root)
def checked(name,path):
 report=e/(name+".json");r=json.loads(report.read_text());a=r["_audit"];g=json.loads((e/(name+"-resource.json")).read_text())
 assert r["isError"] is False
 assert a["upstream_before"]==a["upstream_after"]==upstream,"Upstream snapshot mismatch"
 assert a["base"]==INTEGRATION and a["original_frozen_base"]==census.BASE
 assert a["integration_sources_clean"] is True and a["frozen_mapped_sources_clean"] is True
 assert a["tool"]=="lean_diagnostic_messages" and a["arguments"]["file_path"]==str(path.relative_to(root))
 assert a["arguments"].get("interactive") is False
 assert set(a["arguments"])<={"file_path","interactive","timeout_s"}
 assert a["file"]==str(path) and a["source_sha256"]==a["after_sha256"]==sha(path)
 assert a["local_before"]==a["local_after"]==local
 expected={"tests/h62/item2/audit-abi-world/H62AbiWorld/WitnessSchema.lean","tests/h62/item2/audit-abi-world/resume-serial.lakefile.toml","scripts/h62/item2/audit-abi-world/resume_mcp_call.py","scripts/h62/item2/audit-abi-world/resume-bin/lake","lean-toolchain","lakefile.toml","scripts/h62/item2/audit-abi-world/resume_sources.py","scripts/h62/item2/audit-abi-world/prepare_resume_config.py","scripts/h62/item2/audit-abi-world/census.py"}
 assert set(a["support_before"])==expected and a["support_before"]==a["support_after"]
 assert all(sha(root/p)==h for p,h in a["support_before"].items())
 assert a["lean_version"]=="Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)"
 assert a["lean_num_threads"]==g["lean_num_threads"]==1
 assert g["guard_sha256"]==sha(root/"scripts/h62/item2/audit-abi-world/bounded.py")
 assert g["stdout_file"]==str(report.resolve()) and g["stdout_sha256"]==sha(report)
 assert g["command"][:4]==[".venv/bin/python","-B","scripts/h62/item2/audit-abi-world/resume_mcp_call.py","lean_diagnostic_messages"]
 assert len(g["command"])==5 and json.loads(g["command"][4])==a["arguments"]
 assert g["exit_code"]==0 and g["reason"] is None and g["cleanup_complete"] is True and g["subreaper"] is True
 assert g["swap_active_seen"] is False and g["max_heavy_lean_jobs"]<=1
 assert g["hard_cgroup_limit_bytes"]==16*1024**3 and g["address_space_limit"] is None
 assert g["reserve_bytes"]==4*1024**3 and g["minimum_available_bytes"]>=g["reserve_bytes"]
 assert g["task_cap_bytes"]==12*1024**3 and g["peak_task_rss_bytes"]<=g["task_cap_bytes"]
 d=r["structuredContent"]["result"]
 assert d.get("success") is True and d.get("partial") is False and d.get("timed_out") is False and not d.get("failed_dependencies")
 for item in d["items"]:
  assert item["severity"]!="error"
  if "depends on axioms:" in item["message"]:
   m=re.search(r"depends on axioms: \[([^\]]*)\]",item["message"]);assert m
   assert {x.strip() for x in m[1].split(",") if x.strip()}<={"propext","Classical.choice","Quot.sound"}
 return d
reports={p.stem:checked(p.stem,p) for p in sorted(folder.glob("*.lean"))}
checked("KeySort",root/"Solidity/KeySort.lean")
originals=[d for path in census.module_paths(census.frozen(census.MAP)) for d in census.declarations(path,census.frozen(path))]
fidelity=[json.loads(i["message"][9:]) for i in reports["Fidelity"]["items"] if i["message"].startswith("FIDELITY ")]
assert len(fidelity)==177 and {r["original"] for r in fidelity}=={d["name"] for d in originals}
assert len({r["original"] for r in fidelity})==177 and all(r["matched"] is True for r in fidelity)
assert sum(r["binder_count"] for r in fidelity)==439
success=reports["SuccessContracts"]["items"]
expected_success={"return_total","supported_nonempty","reject_all_fails","always_revert_fails","checked_add_assembly_total","panic_handler_total","zero_receiver_fails"}
assert {i["message"].split("'")[1].removeprefix("H62.AbiWorld.Success.") for i in success if "axioms" in i["message"]}==expected_success
encoded=[json.loads(i["message"][12:]) for i in reports["RuntimeVectors"]["items"] if i["message"].startswith("H62_VECTORS=")]
assert len(encoded)==1
snapshot=args.frozen_evidence or e.parent/"checkpoints/retirement-final"
manifest_path="tests/h62/item2/audit-abi-world/evidence.sha256"
frozen_manifest=subprocess.check_output(["git","show",INTEGRATION+":"+manifest_path],cwd=root)
assert (root/manifest_path).read_bytes()==frozen_manifest,"Archived manifest changed"
manifest=dict((line.split("  ",1)[1],line.split("  ",1)[0]) for line in frozen_manifest.decode().splitlines() if "  " in line and not line.startswith("#"))
for name in ("runtime-vectors.json","reference-replay.json"):
 path=snapshot/name
 keys=[key for key in manifest if Path(key).parts[-3:]==("checkpoints","retirement-final",name)]
 assert len(keys)==1 and sha(path)==manifest[keys[0]]
assert encoded[0]==json.loads((snapshot/"runtime-vectors.json").read_text())
external=json.loads((snapshot/"reference-replay.json").read_text());assert external["status"]=="pass"
assert external["runnerSha256"]==sha(root/"scripts/h62/item2/audit-abi-world/replay.mjs")
print(json.dumps(dict(integration=INTEGRATION,original_base=census.BASE,modules=9,witnesses=177,fidelity=177,binders=439,success_theorems=7,encoded_external_fixtures_identical=10,new_axioms=0,full_gate="separate",boundary="Current Lean checks and exact archived external fixture reuse; no new gas/fork proof or reference execution")))
