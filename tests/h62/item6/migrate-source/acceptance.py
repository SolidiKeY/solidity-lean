#!/usr/bin/env python3
"""Independent import reconciliation and scanner negative controls; no Lean."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
sys.dont_write_bytecode=True
root=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location("census",root/"scripts/h62/item6/migrate-source/census.py")
c=importlib.util.module_from_spec(spec); spec.loader.exec_module(c)
assert c.imports("/- import False /- import False -/ -/\nimport A B -- import False\n") == ["A","B"]
assert c.imports('def s := "import False"\n-- import False\nimport A\n') == ["A"]
assert c.imports('public import A\nprivate meta import B\n') == ["A","B"]
assert c.mask("/- a\n/-b-/\nc-/").count("\n") == 2
census=json.loads(Path(sys.argv[1]).read_text())
tracked=subprocess.check_output(["git","-C",str(root),"ls-tree","-r","--name-only",c.BASE,"Solidity/Source"],text=True).splitlines()
assert sorted(f["path"] for f in census["files"]) == sorted(p for p in tracked if p.endswith(".lean"))
order=census["serial_build_order"]; pos={m:i for i,m in enumerate(order)}
assert {f["module"] for f in census["files"]} <= set(pos)
for m in order:
    text=subprocess.check_output(["git","-C",str(root),"show",c.BASE+":"+m.replace(".","/")+".lean"],text=True)
    # Independent raw header reconciliation: this pin uses one import per line.
    raw=[line.split()[1] for line in text.split("/-!",1)[0].splitlines() if line.startswith("import ")]
    assert raw == c.imports(text),m
    for dep in raw:
        if dep in pos: assert pos[dep] < pos[m],(m,dep)
assert not [m for m in census["nonlocal_imports"] if not m.startswith(("Lean", "Std", "Init"))],census["nonlocal_imports"]
assert len(order)==len(set(order))
print(f"PASS scanner negative controls; all {len(tracked)} Source files; all {len(order)} import headers reconciled; acyclic build order; no unresolved local imports")
