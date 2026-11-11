#!/usr/bin/env python3
"""Provisional unapproved Packing experiment. Caller holds writer lock; fetch cache first.

Fresh serial -j1 Lean checks, no systemd scope (H232). Existing imports are
prepared outside timing; source hashes, actual versions and every guard receipt
are recorded outside the code branch. Does not establish owner approval or TV
replacement coverage. No resource refusal or proof budget is changed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
from views import PROTOTYPE, PACKING, ADDED, CONSUMERS

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("worktree", type=Path)
parser.add_argument("evidence", type=Path)
parser.add_argument("--lean-bin", type=Path, required=True)
parser.add_argument("--rounds", type=int, default=3)
args = parser.parse_args()
assert args.rounds > 0
root, evidence = args.worktree.resolve(), args.evidence.resolve()
evidence.mkdir(parents=True, exist_ok=True)
here = Path(__file__).resolve().parent
pinned = json.loads((here / "views.json").read_text())
assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip() == PROTOTYPE
assert not subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], cwd=root, text=True).strip()
for item in [pinned["before"], *pinned["after"]["modules"], *pinned["consumers_unchanged"]]:
    assert hashlib.sha256((root/item["path"]).read_bytes()).hexdigest() == item["sha256"], item["path"]
env = dict(os.environ, PATH=str(args.lean_bin.resolve())+":"+os.environ["PATH"], LEAN_NUM_THREADS="1")
versions = {name: subprocess.check_output([name, "--version"], env=env, text=True).strip() for name in ["lean", "lake"]}
assert "4.24.0" in versions["lean"] and "797c613" in versions["lean"]
assert "5.0.0-src+797c613" in versions["lake"]

def checked(label, command):
    record = evidence/(label+".json")
    with record.with_suffix(".log").open("w") as log:
        child = subprocess.run([sys.executable, str(here/"bounded.py"), str(record), *command], cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT)
    receipt = json.loads(record.read_text())
    print(label, receipt["exit"], receipt.get("seconds"), flush=True)
    if child.returncode:
        raise SystemExit(child.returncode)
    return receipt

prepare = ["lake", "build", "Solidity.Yul.Views.Widths", "Solidity.Yul.Views.Regions", "Solidity.Yul.Compilation.WordBlockFramed", "Solidity.Yul.Compilation.Artifact"]
checked("prepare", prepare)
(evidence/"provenance.json").write_text(json.dumps(dict(prototype_commit=PROTOTYPE, versions=versions, source_hashes_verified=True, prepare=prepare, systemd_scope=False, status="provisional_unapproved", timing_boundary="Fresh family source checks with existing shared imports prepared symmetrically outside sums; downstream checks separately reported."), indent=2)+"\n")

def mirror(source, target):
    target.mkdir(parents=True, exist_ok=True)
    for path in source.iterdir():
        dest = target/path.name
        if dest.exists():
            if dest.is_dir() and not dest.is_symlink():
                mirror(path, dest)
        else:
            dest.symlink_to(path, target_is_directory=path.is_dir())

results = {}
for mode in ["before", "after"]:
    cache = root/".lake/refactor-cache/tv-yul"/("packing-"+mode)
    (cache/"Solidity/Yul/Views").mkdir(parents=True, exist_ok=True)
    (cache/"prototypes").mkdir(exist_ok=True)
    mirror(root/".lake/build/lib/lean/Solidity", cache/"Solidity")
    env["LEAN_PATH"] = str(cache)
    rounds = []
    for repeat in range(args.rounds):
        receipts = []
        for index, source in enumerate([PACKING] if mode == "before" else ADDED):
            relative = source.removeprefix("prototypes/shadow/")
            output = cache/(relative[:-5]+".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            if output.is_symlink():
                output.unlink()
            options = ["--root=prototypes/shadow"] if source.startswith("prototypes/shadow/") else []
            receipts.append(checked(mode+"-"+str(repeat)+"-"+str(index), ["lean", "-j1", "--tstack=131072", *options, source, "-o", str(output)]))
        rounds.append(dict(seconds=sum(r["seconds"] for r in receipts), records=receipts))
    consumers = []
    for index, source in enumerate(CONSUMERS):
        output = cache/(source[:-5]+".olean")
        if output.is_symlink():
            output.unlink()
        consumers.append(checked(mode+"-consumer-"+str(index), ["lean", "-j1", "--tstack=131072", source, "-o", str(output)]))
    results[mode] = dict(rounds=rounds, median_seconds=statistics.median(r["seconds"] for r in rounds), unchanged_consumers=consumers)
(evidence/"matched-kernel.json").write_text(json.dumps(results, indent=2)+"\n")
