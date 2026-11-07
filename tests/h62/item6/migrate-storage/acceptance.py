#!/usr/bin/env python3
"""Adversarial scanner controls; no Lean/proof acceptance claim."""
import importlib.util,pathlib,sys,tempfile
root=pathlib.Path(__file__).resolve().parents[4]
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location("census",root/"scripts/h62/item6/migrate-storage/census.py")
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
assert c.imports("/- import Bad /- nested -/ -/\nimport A B -- import Bad\npublic import C\nmeta import Lean") == ["A","B","C","Lean"]
assert c.strip_comments('def x := "-- not a comment /-"\n-- hidden\n').splitlines()[0]=='def x := "-- not a comment /-"'
try:c.strip_comments("/- open")
except AssertionError:pass
else:raise AssertionError("unterminated comment accepted")
assert c.closure({"A":["B","C"],"B":["C"],"C":[]},["A"])==["C","B","A"]
try:c.closure({"A":["B"],"B":["A"]},["A"])
except AssertionError:pass
else:raise AssertionError("cycle accepted")
x="\n\nprivate theorem identity : True := by trivial\n"
m=c.DECL.search(x);assert m[1]=="theorem" and m[2]=="identity" and x.count("\n",0,m.start(1))+1==3
with tempfile.TemporaryDirectory(prefix="storage-scanner-controls-") as tmp:
 r=pathlib.Path(tmp);a=r/"Owned.lean";b=r/"External.lean"
 a.write_text("theorem p : True := by trivial");b.write_text("set_option maxHeartbeats 10")
 expected={"Owned.lean":c.digest(a.read_bytes()),"External.lean":c.digest(b.read_bytes())}
 assert c.frozen_matches(r,expected)
 a.write_text("theorem p : False := by trivial")
 assert not c.frozen_matches(r,expected),"owned statement drift accepted"
 a.write_text("theorem p : True := by trivial");b.write_text("set_option maxHeartbeats 20")
 assert not c.frozen_matches(r,expected),"external budget drift accepted"
 b.unlink();assert not c.frozen_matches(r,expected),"missing external accepted"
print("SCANNER_NEGATIVE_CONTROLS_PASS (comments, strings, multi-imports, cycle rejection, positions, owned/external file drift and missing inputs)")
