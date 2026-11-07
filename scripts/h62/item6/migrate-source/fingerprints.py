#!/usr/bin/env python3
"""Deterministic old API/source fingerprints. Raw Expr hashes are not API proof.
Usage: fingerprints.py CENSUS COMPLETE_API OUTPUT_DIRECTORY [SOURCE_ROOT]
"""
import hashlib
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent))
from build import headroom
headroom()
census=json.loads(Path(sys.argv[1]).read_text())
ledger=json.loads(Path(sys.argv[2]).read_text())
out=Path(sys.argv[3]);root=Path(sys.argv[4]) if len(sys.argv)>4 else Path.cwd()
if ledger.get("complete") is not True or ledger["assigned_module_count"]!=census["assigned_count"] or set(ledger["requested_modules"])!={f["module"] for f in census["files"]}:
    raise SystemExit("complete exact assigned-module ledger required")
rows=[{"module":r["module"],"name":r["name"],"kind":r["kind"],"sha256":hashlib.sha256(json.dumps(r,sort_keys=True,ensure_ascii=False,separators=(",",":")).encode("utf-8")).hexdigest()} for r in ledger["rows"]]
for f in census["files"]:
    if hashlib.sha256((root/f["path"]).read_bytes()).hexdigest()!=f["sha256"]: raise SystemExit("source differs from census: "+f["path"])
result={"schema":1,"base":census["base"],"toolchain":"leanprover/lean4:v4.24.0","complete_old_inventory":True,"entries":len(rows),"boundary":"hashes of raw compiler-format type records, not cross-version API equivalence","rows":rows}
out.mkdir(parents=True,exist_ok=True)
(out/"frozen-interfaces-old.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
(out/"frozen-source-files.sha256").write_text("".join(f["sha256"]+"  "+f["path"]+"\n" for f in census["files"]))
headroom()
print("PASS deterministic fingerprints:",len(rows),"declarations /",census["assigned_count"],"unchanged Source files")
