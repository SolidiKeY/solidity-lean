#!/usr/bin/env python3
"""Compare frozen Raw parser nodes with an authenticated external snapshot.

This records syntax and source identity, not semantic equivalence or proofs.
The snapshot must be supplied by the caller; this helper does not read Git refs.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
import re
import signal
import subprocess
import time
from pathlib import Path
import raw_census as base
import raw_syntax as syntax

LEAN = "/workspace/.setup/tools/lean-4.24.0-linux/bin/lean"
PIN = base.ROOT / "tests/h55/vectors-tables/master-raw-source-manifest.json"
PATTERN = re.compile(r"Solidity/Yul/Raw[^/]+\.lean")

def sha(data): return hashlib.sha256(data).hexdigest()
def snapshot(root, expected=None):
    root = root.resolve()
    if root.is_relative_to(base.ROOT): raise ValueError("snapshot must be external")
    meta = json.loads((root / "SOURCE.json").read_text())
    if type(meta) is not dict or set(meta) != {"commit", "files"} or not isinstance(meta["commit"],str) or not re.fullmatch("[0-9a-f]{40}",meta["commit"]) or type(meta["files"]) is not dict: raise ValueError("snapshot metadata schema")
    if expected is None: expected = json.loads(PIN.read_text())
    if meta != expected: raise ValueError("snapshot differs from pinned manifest")
    paths = sorted(meta["files"])
    if any(not PATTERN.fullmatch(p) for p in paths): raise ValueError("snapshot path schema")
    actual = sorted(str(p.relative_to(root)) for p in (root / base.AREA).glob("Raw*.lean"))
    if actual != paths: raise ValueError("snapshot inventory")
    for path in paths:
        if sha((root/path).read_bytes()) != meta["files"][path]: raise ValueError("snapshot source hash")
    return meta, paths

def avail():
    with open("/proc/meminfo") as f: host=int(next(line.split()[1] for line in f if line.startswith("MemAvailable:")))
    limit=Path("/sys/fs/cgroup/memory.max").read_text().strip(); current=int(Path("/sys/fs/cgroup/memory.current").read_text())
    return min(host,(int(limit)-current)//1024) if limit!="max" else host

def run(root, output):
    _, paths=snapshot(root); output=output.resolve()
    if output.exists() or output.is_relative_to(base.ROOT): raise ValueError("new external output required")
    if avail()<4194304: raise RuntimeError("less than 4 GiB available")
    cmd=[LEAN,"-j1","--tstack=131072","--root="+str(base.ROOT),"--run",str(base.ROOT/"scripts/h55/vectors-tables/ParseProbe.lean"),*paths]
    with output.open("x") as out:
        with subprocess.Popen(cmd,cwd=root,env=dict(os.environ,LEAN_NUM_THREADS="1"),stdout=out,stderr=subprocess.STDOUT,start_new_session=True) as proc:
            while proc.poll() is None:
                if avail()<4194304:
                    os.killpg(proc.pid,signal.SIGTERM); proc.wait(); raise RuntimeError("resource guard stopped parser")
                time.sleep(0.5)
            if proc.returncode: raise RuntimeError(f"parser exited {proc.returncode}")
    print(f"PASS: {len(paths)} snapshot files parsed")

def parse(text, root, paths):
    lines=iter(text.splitlines()); result={}
    for path in paths:
        if next(lines,None)!="FILE "+path: raise ValueError("file order or inventory")
        data=(root/path).read_bytes(); nodes=[]
        for line in lines:
            if line=="END "+path: break
            m=syntax.NODE.fullmatch(line)
            if not m: raise ValueError("node schema")
            kind,start,end=m.group(1),int(m.group(2)),int(m.group(3))
            if not 0<=start<end<=len(data): raise ValueError("node span")
            nodes.append({"kind":kind,"start":start,"end":end,"source_sha256":sha(data[start:end])})
        else: raise ValueError("missing end")
        result[Path(path).name]=nodes
    if next(lines,None) is not None: raise ValueError("extra node or file")
    return result

def compare(root, log, baseline_log):
    meta,paths=snapshot(root)
    old=syntax.parse_log(baseline_log.read_text())
    old_meta=json.loads(base.MANIFEST.read_text())["files"]
    new=parse(log.read_text(),root,paths)
    new_names=set(new); old_names=set(old)
    changed=[]
    for name in sorted(new_names & old_names):
        if meta["files"]["Solidity/Yul/"+name] != old_meta[name]["sha256"]: changed.append(name)
    common_unchanged=sorted((new_names & old_names)-set(changed))
    for name in common_unchanged:
        if new[name] != old[name]: raise ValueError("parser nodes changed for identical source")
    def counts(nodes): return dict(sorted(Counter(n["kind"] for n in nodes).items()))
    diff={}
    for name in changed:
        diff[name]={"base_sha256":old_meta[name]["sha256"],"master_sha256":meta["files"]["Solidity/Yul/"+name],"base_nodes":counts(old[name]),"master_nodes":counts(new[name]),"node_content_equal": [(n["kind"],n["source_sha256"]) for n in old[name]] == [(n["kind"],n["source_sha256"]) for n in new[name]]}
    return {"base":base.BASE,"master":meta["commit"],"base_files":len(old),"master_files":len(new),"added":sorted(new_names-old_names),"removed":sorted(old_names-new_names),"changed":diff,"unchanged_files_verified":len(common_unchanged),"base_totals":counts([node for nodes in old.values() for node in nodes]),"master_totals":counts([node for nodes in new.values() for node in nodes]),"added_nodes":{name:counts(new[name]) for name in sorted(new_names-old_names)}}

def main():
    p=argparse.ArgumentParser(); p.add_argument("mode",choices=("run","compare")); p.add_argument("snapshot",type=Path); p.add_argument("log",type=Path); p.add_argument("--baseline-log",type=Path); p.add_argument("--output",type=Path); a=p.parse_args()
    if a.mode=="run":
        if a.baseline_log is not None or a.output is not None: p.error("unexpected options")
        run(a.snapshot,a.log); return
    if a.baseline_log is None or a.output is None: p.error("baseline log and output required")
    out=a.output.resolve()
    if out.exists() or out.is_relative_to(base.ROOT): raise ValueError("new external output required")
    result=compare(a.snapshot,a.log,a.baseline_log)
    out.write_text(json.dumps(result,indent=2)+"\n")
    print(f"PASS: {result['base_files']} frozen and {result['master_files']} snapshot files compared; {len(result['added'])} added, {len(result['changed'])} changed")

if __name__ == "__main__": main()
