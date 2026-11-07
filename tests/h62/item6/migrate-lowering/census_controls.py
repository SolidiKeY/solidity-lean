#!/usr/bin/env python3
"""Regression controls for review-discovered census omissions and false import edges."""
import importlib.util, tempfile
from pathlib import Path
spec=importlib.util.spec_from_file_location("census",Path(__file__).resolve().parents[4]/"scripts/h62/item6/migrate-lowering/census.py")
m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
assert m.uncomment("import/- -/A") == "import  A"
assert "Hidden" not in m.uncomment("/- outer /- nested -/ import Hidden -/")
# Use a real temporary Git tree because the census records its exact HEAD.
import subprocess
with tempfile.TemporaryDirectory() as d:
    root=Path(d); p=root/"Solidity/Lowering/Test.lean"; p.parent.mkdir(parents=True)
    p.write_text("import Solidity.Dependency\n/- import Solidity.Hidden -/\nlocal instance : Decidable True := inferInstance\nprivate instance named : Decidable True := inferInstance\nexample : True := by trivial\nderiving instance DecidableEq for Nat\nattribute [instance] named\n")
    dep=root/"Solidity/Dependency.lean"; dep.write_text("def answer : Nat := 42\n")
    subprocess.run(["git","init","-q",d],check=True)
    subprocess.run(["git","-C",d,"-c","user.name=Control","-c","user.email=control@example.invalid","commit","--allow-empty","-qm","fixture"],check=True)
    c=m.census(root)
    assert len(c["modules"][0]["api_directives"]) == 2
    assert c["closure_order"] == ["Solidity.Dependency", "Solidity.Lowering.Test"]
    assert c["direct_external_edges"]==[{"from":"Solidity.Lowering.Test","to":"Solidity.Dependency"}]
    assert [x["kind"] for x in c["modules"][0]["declarations_lexical"]]==["instance","instance","example"]
    dep.write_text("import Solidity.Lowering.Test\n")
    try: m.census(root)
    except ValueError as e: assert "import cycle" in str(e)
    else: raise AssertionError("cycle accepted")
print("PASS: local/private instances, examples, comment imports, dependency order, cycle rejection")
