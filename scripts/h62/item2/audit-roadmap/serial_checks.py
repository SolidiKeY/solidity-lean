#!/usr/bin/env python3
"""Bounded serial exact-source Lean checks with isolated outputs, never caches.
This is targeted evidence only, not a replacement for run-lean.sh final gates.
"""
import argparse
import hashlib
import json
import os
import pathlib
import re
import resource
import subprocess
import time

ap = argparse.ArgumentParser()
ap.add_argument("--lean", required=True, type=pathlib.Path)
ap.add_argument("--output", required=True, type=pathlib.Path)
ap.add_argument("--target", choices=("all", "audit", "evm", "context", "frontend", "creation"), default="all")
args = ap.parse_args()
root = pathlib.Path(__file__).resolve().parents[4]
out = args.output.resolve()
if out.is_relative_to(root):
    raise SystemExit("H44: outputs must be off git")
out.mkdir(parents=True,exist_ok=True)
lib = out/"olean"
lib.mkdir(exist_ok=True)
pin_path = pathlib.Path("/workspace/h62-coordinator-inputs/toolchain-pin.json")
pin = json.loads(pin_path.read_text())
archive = args.lean.resolve().parents[3]/pin["asset"]
archive_hash = hashlib.file_digest(archive.open("rb"), "sha256").hexdigest()
if archive_hash != pin["sha256"]:
    raise SystemExit("official archive checksum mismatch")
compiler_hash = hashlib.sha256(args.lean.resolve().read_bytes()).hexdigest()
pin_hash = hashlib.sha256(pin_path.read_bytes()).hexdigest()
records = []
env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(lib))

def limit(budget):
    resource.setrlimit(resource.RLIMIT_AS, (budget,budget))
    resource.setrlimit(resource.RLIMIT_CORE, (0,0))

def run(label, cmd):
    available = int(re.search(r"MemAvailable:\s+(\d+)",pathlib.Path("/proc/meminfo").read_text())[1])*1024
    cg = pathlib.Path("/sys/fs/cgroup")
    cap = int((cg/"memory.max").read_text())
    used = int((cg/"memory.current").read_text())
    if available < 4*1024**3 or cap-used < 4*1024**3:
        raise SystemExit("resource guard: less than 4 GiB available reserve")
    budget = min(12*1024**3, available-4*1024**3, cap-used-4*1024**3)-256*1024**2
    if budget < 1024**3:
        raise SystemExit("resource guard: less than 1 GiB job budget after reserve")
    log = out/(label.replace("/","_")+".log")
    start = time.monotonic()
    with log.open("w") as f:
        try:
            result = subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT,
                timeout=300,preexec_fn=lambda: limit(budget))
            code = result.returncode
        except subprocess.TimeoutExpired:
            code = 124
    row = dict(label=label,command=cmd,exit=code,compiler_sha256=compiler_hash,
        toolchain_pin_sha256=pin_hash, official_archive_sha256=archive_hash,seconds=round(time.monotonic()-start,3),
        log=str(log),memory_address_space_bytes=budget,threads=1,
        cgroup_free_at_start=cap-used,host_available_at_start=available,
        swap_total_kib=int(re.search(r"SwapTotal:\s+(\d+)",pathlib.Path("/proc/meminfo").read_text())[1]))
    if cmd[-1].endswith(".lean") and (root/cmd[-1]).is_file():
        row["source_sha256"] = hashlib.sha256((root/cmd[-1]).read_bytes()).hexdigest()
    records.append(row)
    (out/"results.json").write_text(json.dumps(records,indent=2)+"\n")
    print(json.dumps(row),flush=True)
    return code

seen = set()
def compile_module(path):
    if path in seen:
        return
    data = (root/path).read_text()
    for mod in re.findall(r"^import\s+(\S+)",data,re.M):
        dep = mod.replace(".","/")+".lean"
        if (root/dep).exists():
            compile_module(dep)
    target = lib/pathlib.Path(path).with_suffix(".olean")
    target.parent.mkdir(parents=True,exist_ok=True)
    cmd = [str(args.lean.resolve()),"-j1","-M11264","--tstack=131072","-o",str(target),path]
    code = run(path,cmd)
    if code:
        raise SystemExit(code)
    seen.add(path)

for label, binary in (("lean-version", args.lean.resolve()), ("lake-version", args.lean.resolve().with_name("lake"))):
    if run(label,[str(binary),"--version"]):
        raise SystemExit("toolchain version command failed")
compile_module("Solidity/KeySort.lean")
if args.target == "all":
    compile_module("SolkeyCheck.lean")
    key = "/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key"
    code = run("solkeycheck",[str(args.lean.resolve()),"-j1","-M11264","--tstack=131072","--run","SolkeyCheck.lean","--key",key])
    if code:
        raise SystemExit(code)
audit_file = {"evm": "EvmWitnesses.lean", "context": "ContextWitnesses.lean", "frontend": "FrontendWitnesses.lean", "creation": "CreationWitnesses.lean"}.get(args.target, "WitnessObstruction.lean")
compile_module("tests/h62/item2/audit-roadmap/" + audit_file)
