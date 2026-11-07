#!/usr/bin/env python3
"""Deterministic census acceptance against the frozen git tree, never a runtime gate."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

here=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("census",here/"census.py")
c=importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
subprocess.run([sys.executable,"-B",str(here/"test_census.py")],check=True,cwd=c.ROOT)
def require(condition, message):
    if not condition: raise SystemExit("FAIL: "+message)

result=c.census()
manifest=json.loads(c.DEST.read_text())
rendered=json.dumps(result,ensure_ascii=False,indent=2)+"\n"
require(c.digest(rendered)==manifest["inventory_sha256"],"inventory drift")
require(result["totals"]==manifest["totals"],"counts drift")
require(result["files"]==manifest["files"],"file pins drift")
paths=subprocess.check_output(["git","ls-tree","-r","--name-only",c.BASE,"--",c.FAMILY],cwd=c.ROOT,text=True).splitlines()
require(paths==[f["path"] for f in result["files"]],"frozen file set differs")
for f in result["files"]:
    source=subprocess.check_output(["git","show",c.BASE+":"+f["path"]],cwd=c.ROOT)
    require(hashlib.sha256(source).hexdigest()==f["sha256"],"frozen source differs: "+f["path"])
require(all("." in r["name"] for r in result["declarations"]),"unqualified declaration")
print("FROZEN_FAMILY_SOURCE_IDENTITY_PASS: 230/230 files; no original edited")
print("CENSUS_ACCEPTANCE_PASS: "+manifest["inventory_sha256"])
print("Boundary: textual inventory only; semantic cases, correspondence and Lean gates are separate.")
