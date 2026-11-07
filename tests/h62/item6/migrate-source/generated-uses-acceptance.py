#!/usr/bin/env python3
"""Negative controls for the bounded direct-use census; no Lean invocation."""
import importlib.util
from pathlib import Path
import sys
sys.dont_write_bytecode=True
root=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(root/"scripts/h62/item6/migrate-source"))
s=importlib.util.spec_from_file_location("generated_uses",root/"scripts/h62/item6/migrate-source/generated-uses.py")
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
text='/- R.noConfusion /- T.recOn -/ -/\n-- D.casesOn\ndef t := "X.match_1"\ntheorem keep (ρ : R) : ρ.ctorIdx = 0 := by\n  exact R.noConfusion h\n'
u=m.uses(text)
assert [(r["line"],r["token"]) for r in u]==[(4,"ρ.ctorIdx"),(5,"R.noConfusion")]
assert all(r["enclosing_declaration_candidate"]["token"]=="keep" for r in u)
assert not m.uses("def Foo.recOn := 0\n")
assert not m.uses("def x := Foo.noConfusionSuffix\n")
assert [r["token"] for r in m.uses("exact Option.some.injEq h\nexact Tree.rec x\n")] == ["Option.some.injEq","Tree.rec"]
print("PASS direct-use census negative controls: comments/nested comments/strings, Unicode receiver, declaration exclusion, token boundary and constructor injectivity")
