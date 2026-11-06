#!/usr/bin/env python3
"""Deterministic byte census. This is source coverage, not a Lean declaration audit."""
import argparse, hashlib, json, pathlib, subprocess
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])
def snapshot(root, revision=None):
    names = (git(root, "ls-tree", "-rz", "--name-only", revision, "Bridge/") if revision else git(root, "ls-files", "-z", "--cached", "Bridge/")).decode().split("\0")
    rows = []
    for name in sorted(set(n for n in names if n.endswith(".lean"))):
        if not revision and not (root / name).exists():
            continue
        data = git(root, "show", revision + ":" + name) if revision else (root / name).read_bytes()
        rows.append({"path":name,"bytes":len(data),"sha256":hashlib.sha256(data).hexdigest()})
    return rows
def compare(before, after):
    a = {r["path"]:r for r in before}; b = {r["path"]:r for r in after}
    return {"removed":sorted(a.keys()-b.keys()),"added":sorted(b.keys()-a.keys()),
            "changed":sorted(k for k in a.keys() & b.keys() if a[k]!=b[k])}
def main():
    ap=argparse.ArgumentParser(description=__doc__); ap.add_argument("--root",type=pathlib.Path,default=pathlib.Path.cwd())
    ap.add_argument("--baseline",default=BASE); ap.add_argument("--require-unchanged",action="store_true"); args=ap.parse_args()
    before=snapshot(args.root,args.baseline); after=snapshot(args.root); delta=compare(before,after)
    print(json.dumps({"schema":1,"baseline":args.baseline,"boundary":"All tracked Bridge Lean source bytes; no elaboration or theorem equivalence claim",
                      "files":before,"current_delta":delta},indent=2,sort_keys=True))
    return int(args.require_unchanged and any(delta.values()))
if __name__=="__main__": raise SystemExit(main())
