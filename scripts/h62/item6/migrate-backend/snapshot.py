#!/usr/bin/env python3
"""Reproduce the scope and frozen-source evidence, and hash off-git bulk files."""
import argparse
import fcntl
import hashlib
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--evidence", type=Path, required=True)
args = parser.parse_args()
lockpath = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
lockpath.parent.mkdir(parents=True, exist_ok=True)
lock = lockpath.open("a")
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
root = Path.cwd()
evidence = args.evidence.resolve()
inputs = Path("/workspace/h62-coordinator-inputs")
for name, expected in json.loads((inputs/"sha256.json").read_text()).items():
    if hashlib.sha256((inputs/name).read_bytes()).hexdigest() != expected:
        raise RuntimeError("coordinator input checksum mismatch: " + name)
registry = json.loads((inputs/"ownership.json").read_text())
records = []
def walk(value):
    if isinstance(value, dict):
        if value.get("owner") == "solidity-h62-6-20261106/migrate-backend": records.append(value)
        for item in value.values(): walk(item)
    elif isinstance(value, list):
        for item in value: walk(item)
walk(registry)
if len(records) != 1: raise RuntimeError("migration ownership record is ambiguous")
allowed = sorted(s.strip() for s in records[0]["writeScope"].split(";") if s.strip().endswith(".lean"))
actual = sorted(str(p) for p in Path("Solidity/Backend").rglob("*.lean"))
if allowed != actual: raise RuntimeError("assigned scope differs from Backend tree")
files = [{"path":p,"sha256":hashlib.sha256(Path(p).read_bytes()).hexdigest()} for p in actual]
base = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
subprocess.run(["git","diff","--exit-code",base,"--","Solidity","lean-toolchain","lakefile.toml"],check=True)
info = json.loads((evidence/"census-base.json").read_text())
summary = {"base":base,"scope_matches":True,"assigned_files":len(files),
           "closure_modules":info["closure_count"],"external_local_modules":len(info["external_local_closure"]),
           "cross_directory_edges":len(info["cross_directory_edges"]),
           "source_tree":subprocess.check_output(["git","rev-parse",base+":Solidity/Backend"],text=True).strip(),
           "source_files":files,"boundary":"Whole-file byte hashes, not elaborated type/interface compatibility proof",
           "baseline_trust_tokens":{key:sum(row["trust_tokens"][key] for row in info["files"]) for key in ("sorry","axiom","native_decide")}}
(evidence/"scope-and-source-freeze.json").write_text(json.dumps(summary,indent=2,sort_keys=True)+"\n")
manifest = []
for path in sorted(evidence.rglob("*")):
    if path.is_file() and path.name != "BULK.sha256":
        with path.open("rb") as stream: digest = hashlib.file_digest(stream,"sha256").hexdigest()
        manifest.append(digest+"  "+str(path.relative_to(evidence)))
(evidence/"BULK.sha256").write_text("\n".join(manifest)+"\n")
print(json.dumps({k:summary[k] for k in ("scope_matches","assigned_files","closure_modules","external_local_modules","cross_directory_edges","baseline_trust_tokens")}))
