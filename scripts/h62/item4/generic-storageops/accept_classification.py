#!/usr/bin/env python3
"""Accept complete source-contract audit; deliberately separate from Lean gates."""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

here=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("classification",here/"classify.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
p=argparse.ArgumentParser()
p.add_argument("--output",type=Path,required=True)
a=p.parse_args()
if a.output.resolve().is_relative_to(m.c.ROOT): p.error("bulk audit must stay off git")
for name in ("accept.py","test_classify.py"):
    subprocess.run([sys.executable,"-B",str(here/name)],cwd=m.c.ROOT,check=True)
result=m.classify();inventory=m.c.census();m.validate(result,inventory)
rendered=json.dumps(result,ensure_ascii=False,indent=2)+"\n"
pins=json.loads(m.MANIFEST.read_text())
if m.c.digest(rendered)!=pins["classification_sha256"]: raise SystemExit("FAIL: classification pin drift")
if pins["totals"]!=result["totals"]: raise SystemExit("FAIL: classification total drift")
if m.c.digest(m.DOMAINS.read_text())!=pins["domains_sha256"]: raise SystemExit("FAIL: domain map drift")
# Reconstruct the prior committed inventory to prove ALL old header pins survived.
legacy=json.loads(json.dumps(inventory));legacy["format"]=1
sources={f["path"]:(m.c.ROOT/f["path"]).read_text() for f in legacy["files"]}
for row in legacy["declarations"]:
    source=sources[row["path"]]
    start=sum(len(line) for line in source.splitlines(keepends=True)[:row["line"]-1])
    code=m.c.mask(source[start:])
    old=source[start:start+m.c.legacy_signature_end(code)].rstrip()
    row["statement"]=old;row["header_sha256"]=m.c.digest(old)
    row["statement_sha256"]=row.pop("legacy_v1_statement_sha256")
legacy_rendered=json.dumps(legacy,ensure_ascii=False,indent=2)+"\n"
legacy_sha="fd5361469fe3e59603d8e1612e5abb306c586ad1a2f97a2576ab7c178179f336"
if m.c.digest(legacy_rendered)!=legacy_sha: raise SystemExit("FAIL: legacy inventory preservation")
a.output.write_text(rendered)
print("ALL_SOURCE_CONTRACTS_CLASSIFIED: 230 files;6036 declarations;1623 public/private control claims")
print("LEGACY_V1_PRESERVATION_PASS: "+legacy_sha)
print("CLASSIFICATION_ACCEPTANCE_PASS: "+pins["classification_sha256"])
print("Boundary: semantic source-contract audit only; equivalence, exact instances and proof/runtime/timing gates remain pending.")
