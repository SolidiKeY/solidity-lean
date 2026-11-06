#!/usr/bin/env python3
"""Scanner negative controls and fail-closed timing acceptance; no Lean server."""
import copy,importlib.util,json,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/"scripts/h62/item6/migrate-syntax"))
from census import inventory,imports,code_only
from compare import compare
assert imports('import Solidity.AST\n/- import writes\n /- nested -/ -/\ndef x := "import Fake"\n-- import Wrong\n')==["Solidity.AST"]
try: code_only('/- unfinished')
except ValueError: pass
else: raise AssertionError("Unclosed comment accepted")
x=inventory(ROOT)
assert len(x["files"])==21 and len(x["build_order"])==29
assert "writes" not in str(x["direct_external_edges"])
r=next(f for f in x["files"] if f["module"]=="Solidity.Syntax.Scoped")
assert {333,1098,1101}<={d["line"] for d in r["declaration_lines"]}
assert any(f["command_lines"] for f in x["files"])
assert x==inventory(ROOT)
with tempfile.TemporaryDirectory() as tmp:
 p=Path(tmp)/"Solidity/Syntax";p.mkdir(parents=True);(p/"X.lean").write_text("import Solidity.Missing\n")
 try: inventory(Path(tmp))
 except ValueError: pass
 else: raise AssertionError("Missing local import accepted")
 (p/"X.lean").write_text("import Solidity.Syntax.X\n")
 try: inventory(Path(tmp))
 except ValueError: pass
 else: raise AssertionError("Cycle accepted")
a=dict(status="pass",expected_modules=1,completed_modules=1,cpu=0,threads=1,lean_memory_mib=11000,reserve_gib=4,swap="none",cache="empty",wall_seconds=100,modules=[dict(module="A",status="pass",max_rss_kib=100)])
assert compare(a,copy.deepcopy(a))["status"]=="pass"
b=copy.deepcopy(a);b["wall_seconds"]=110;assert compare(a,b)["status"]=="ESCALATE"
b=copy.deepcopy(a);b["modules"][0]["max_rss_kib"]=110;assert compare(a,b)["status"]=="ESCALATE"
b=copy.deepcopy(a);b["wall_seconds"]=111;assert compare(a,b)["status"]=="STOP"
b=copy.deepcopy(a);b["modules"][0]["max_rss_kib"]=111;assert compare(a,b)["status"]=="STOP"
for field,value in [("status","running"),("completed_modules",0),("cpu",1)]:
 b=copy.deepcopy(a);b[field]=value
 try: compare(a,b)
 except ValueError: pass
 else: raise AssertionError("Invalid comparison accepted: "+field)
print("PASS: deterministic 21-file/29-module census, attributed declarations, command/case inventory, comment/string controls, missing import/cycle refusal, incomplete/settings mismatch rejection, wall/RSS STOP controls")
