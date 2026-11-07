#!/usr/bin/env python3
"""Associate selected Lean parser nodes with their source declarations.

This is syntax accounting only: project imports are not elaborated and no
parametrisation, proof preservation, or semantic exhaustiveness is established.
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
import raw_master_reconcile as master
import raw_syntax as syntax
import raw_census as base

DECL = re.compile(r"DECL some \{ byteIdx := ([0-9]+) \} some \{ byteIdx := ([0-9]+) \}")
HEAD = re.compile(r"^(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(?:def|theorem|lemma|inductive|structure|abbrev|instance|example|opaque)\b.*",re.M)
MANIFEST = base.ROOT / "tests/h55/vectors-tables/master-raw-context-manifest.json"
def sha(data): return hashlib.sha256(data).hexdigest()

def run(root, output):
    _, paths = master.snapshot(root); output=output.resolve()
    if output.exists() or output.is_relative_to(base.ROOT): raise ValueError("new external output required")
    if master.avail() < 4194304: raise RuntimeError("less than 4 GiB available")
    cmd=[master.LEAN,"-j1","--tstack=131072","--root="+str(base.ROOT),"--run",str(base.ROOT/"scripts/h55/vectors-tables/ParseContext.lean"),*paths]
    with output.open("x") as out:
        with subprocess.Popen(cmd,cwd=root,env=dict(os.environ,LEAN_NUM_THREADS="1"),stdout=out,stderr=subprocess.STDOUT,start_new_session=True) as proc:
            while proc.poll() is None:
                if master.avail()<4194304:
                    os.killpg(proc.pid,signal.SIGTERM); proc.wait(); raise RuntimeError("resource guard stopped parser")
                time.sleep(0.5)
            if proc.returncode: raise RuntimeError(f"parser exited {proc.returncode}")
    print(f"PASS: declaration-context parser exited 0 for {len(paths)} files")

def parse(root, log, reference):
    meta,paths=master.snapshot(root)
    expected=master.parse(reference.read_text(),root,paths)
    lines=iter(log.read_text().splitlines()); result={}
    for path in paths:
        if next(lines,None)!="FILE "+path: raise ValueError("file inventory or order")
        data=(root/path).read_bytes(); decls=[]; active=None; flat=[]
        for line in lines:
            if line=="END "+path:
                if active is not None: raise ValueError("unclosed declaration")
                break
            if m:=DECL.fullmatch(line):
                if active is not None: raise ValueError("nested declaration unsupported")
                start,end=int(m.group(1)),int(m.group(2))
                if not 0<=start<end<=len(data): raise ValueError("declaration span")
                content=data[start:end]; text=content.decode("utf-8"); head=HEAD.search(text)
                if not head: raise ValueError(f"{path}: unrecognized declaration heading")
                active={"start":start,"end":end,"heading":head.group(0),"source_sha256":sha(content),"nodes":[]}
            elif line=="ENDDECL":
                if active is None: raise ValueError("unexpected declaration end")
                decls.append(active); active=None
            elif m:=syntax.NODE.fullmatch(line):
                if active is None: raise ValueError("node outside declaration")
                kind,start,end=m.group(1),int(m.group(2)),int(m.group(3))
                if not active["start"]<=start<end<=active["end"]: raise ValueError("node span outside declaration")
                node={"kind":kind,"start":start,"end":end,"source_sha256":sha(data[start:end])}
                active["nodes"].append(node); flat.append(node)
            else: raise ValueError("context log schema")
        else: raise ValueError("missing file end")
        name=Path(path).name
        if flat != expected[name]: raise ValueError("selected node inventory differs from reference")
        result[name]=decls
    if next(lines,None) is not None: raise ValueError("extra log entries")
    return {"master":meta["commit"],"files":result}

def summary(data):
    files={}
    for name,decls in data["files"].items():
        encoded=json.dumps(decls,ensure_ascii=False,separators=(",", ":")).encode()
        files[name]={"declarations":len(decls),"nodes":sum(len(d["nodes"]) for d in decls),"sha256":sha(encoded)}
    return {"master":data["master"],"files":files}

def main():
    p=argparse.ArgumentParser(); p.add_argument("mode",choices=("run","manifest","extract","check")); p.add_argument("snapshot",type=Path); p.add_argument("log",type=Path); p.add_argument("--reference",type=Path); p.add_argument("--data",type=Path); a=p.parse_args()
    if a.mode=="run":
        if a.reference or a.data: p.error("unexpected options")
        run(a.snapshot,a.log); return
    if a.reference is None: p.error("reference log required")
    result=parse(a.snapshot,a.log,a.reference)
    if a.mode=="manifest":
        if a.data or MANIFEST.exists(): raise ValueError("manifest exists or unexpected data")
        MANIFEST.write_text(json.dumps(summary(result),indent=2)+"\n"); return
    if summary(result)!=json.loads(MANIFEST.read_text()): raise ValueError("context inventory differs")
    if a.data is None: p.error("data required")
    if a.mode=="extract":
        dest=a.data.resolve()
        if dest.exists() or dest.is_relative_to(base.ROOT): raise ValueError("new external data required")
        dest.write_text(json.dumps(result,ensure_ascii=False,separators=(",", ":"))+"\n"); return
    if json.loads(a.data.read_text())!=result: raise ValueError("context data differs")
    print(f"PASS: {len(result['files'])} files, {sum(len(ds) for ds in result['files'].values())} declarations, {sum(len(d['nodes']) for ds in result['files'].values() for d in ds)} selected nodes")

if __name__ == "__main__": main()
