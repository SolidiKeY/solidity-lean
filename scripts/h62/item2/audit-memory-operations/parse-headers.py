#!/usr/bin/env python3
"""Run the pinned Lean source parser under serial audit resource bounds.

No source declarations are elaborated; frozen interfaces are never modified.
The full census is retained. Parser results grant no kernel or witness credit.
"""
import argparse
import hashlib
import importlib.util
import json
import os
import pathlib
import re
import resource
import subprocess
import time

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("--lean",type=pathlib.Path,required=True)
p.add_argument("--census",type=pathlib.Path,required=True)
p.add_argument("--evidence",type=pathlib.Path,required=True)
p.add_argument("--all-theorems",action="store_true")
a = p.parse_args()
root = pathlib.Path.cwd()
evidence = a.evidence.resolve()
evidence.mkdir(parents=True,exist_ok=True)
spec = importlib.util.spec_from_file_location("reconcile",root/"scripts/h62/item2/audit-memory-operations/reconcile.py")
reconcile = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reconcile)
source = json.loads(a.census.read_text())
requests = []
identities = []
for index,row in enumerate(source["declarations"]):
    if row["kind"] not in ("theorem","lemma"): continue
    if not a.all_theorems and row["premise_bundle"]["header_source"]: continue
    region = row["source_command_region"]
    actual=(root/row["path"]).read_text()[row["source_start"]:row["source_end"]]
    if actual!=region: raise SystemExit("Frozen source span mismatch")
    match = re.search(r"\b(?:theorem|lemma)\s+[^\s:(\[{]+",reconcile.census.mask(region))
    if not match: raise SystemExit("Declaration source name absent")
    requests.append(dict(source_id=index,source=region,parse_start_utf8=len(region[:match.end()].encode())))
    identities.append(dict(source_id=index,path=row["path"],line=row["line"],source_name=row["name"]))
if not requests: raise SystemExit("No requested headers; refusing empty success")
input_path=evidence/"parser-input.json"
output_path=evidence/"parser-output.json"
input_path.write_text(json.dumps(dict(requests=requests),ensure_ascii=False)+"\n")
cmd=[str(a.lean.resolve()),"-j1","-M8192","--tstack=131072","tests/h62/item2/audit-memory-operations/HeaderParser.lean"]
def limit(): resource.setrlimit(resource.RLIMIT_AS,(12*1024**3,12*1024**3))
def available():
    mem=dict(line.split(":",1) for line in pathlib.Path("/proc/meminfo").read_text().splitlines())
    host=int(mem["MemAvailable"].split()[0])*1024
    if int(mem["SwapTotal"].split()[0])!=0: raise SystemExit("Swap must be absent")
    cg=pathlib.Path("/sys/fs/cgroup")
    cap=(cg/"memory.max").read_text().strip()
    return host if cap=="max" else min(host,int(cap)-int((cg/"memory.current").read_text()))
if available()<4*1024**3: raise SystemExit("Below 4GiB reserve")
start=time.monotonic(); reason=None
with (evidence/"lean-parser.log").open("w") as log:
    child=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,env=dict(os.environ,LEAN_NUM_THREADS="1",H62_HEADER_INPUT=str(input_path),H62_HEADER_OUTPUT=str(output_path),LEAN_SYSROOT=str(a.lean.resolve().parent.parent),PATH=str(a.lean.resolve().parent)+os.pathsep+os.environ.get("PATH","")),preexec_fn=limit)
    while child.poll() is None:
        if available()<4*1024**3: reason="RESOURCE_BLOCK:4GiB reserve"
        if time.monotonic()-start>300: reason="TIME_BLOCK:300 seconds"
        if reason: child.terminate();break
        try: child.wait(timeout=0.5)
        except subprocess.TimeoutExpired: pass
    try: child.wait(timeout=3)
    except subprocess.TimeoutExpired: child.kill();child.wait()
record=dict(command=cmd,exit=child.returncode,seconds=time.monotonic()-start,
    maxrss_KiB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,blocker=reason,
    census_sha256=hashlib.sha256(a.census.read_bytes()).hexdigest(),identities=identities)
(evidence/"command.json").write_text(json.dumps(record,indent=2)+"\n")
if child.returncode or reason: raise SystemExit(1)
output=json.loads(output_path.read_text())
if [r["source_id"] for r in output["results"]]!=[r["source_id"] for r in requests]: raise SystemExit("Result identity mismatch")
results=[]
for req,result in zip(requests,output["results"]):
    result=dict(result)
    if result["status"]=="source-parsed":
        raw=req["source"].encode()
        end=result["header_end_utf8"]
        if not req["parse_start_utf8"]<end<=len(raw): raise SystemExit("Invalid parser span")
        header=raw[:end].decode()
        remainder=raw[end:].decode().lstrip()
        if not remainder.startswith((":=","|","where")): raise SystemExit("Unexpected proof separator: "+remainder[:80])
        result.update(header_source=header,header_end=len(header),source_region_sha256=hashlib.sha256(raw).hexdigest(),
            header_sha256=hashlib.sha256(header.encode()).hexdigest(),proof_separator=next(s for s in (":=","|","where") if remainder.startswith(s)),
            boundary="Lean parser source signature; inferred/kernel signature remains pending")
    results.append(result)
report=dict(boundary=output["boundary"],census_sha256=record["census_sha256"],identities=identities,results=results,
    counts=dict(requested=len(requests),source_parsed=sum(r["status"]=="source-parsed" for r in results),parse_errors=sum(r["status"]!="source-parsed" for r in results),kernel_signatures=0,simultaneous_witness_credits=0))
(evidence/"headers.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
print(json.dumps(dict(counts=report["counts"],seconds=record["seconds"],maxrss_KiB=record["maxrss_KiB"])))

record["parser_errors"]=report["counts"]["parse_errors"]
record["result_exit"]=1 if record["parser_errors"] else 0
(evidence/"command.json").write_text(json.dumps(record,indent=2)+"\n")
raise SystemExit(record["result_exit"])
