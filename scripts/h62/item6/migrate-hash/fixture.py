#!/usr/bin/env python3
"""Generate migration candidates inside the assigned tests area; originals stay read-only."""
from pathlib import Path
import subprocess
root = Path("tests/h62/item6/migrate-hash")
root.mkdir(parents=True, exist_ok=True)
for name in ("CollisionBound", "Adaptive"):
    s = subprocess.check_output(["git", "show", f"c6f550e281a7e5affa9a99bc2cdaed556dec00e4:Solidity/Hash/{name}.lean"],text=True)
    if name == "CollisionBound":
        s = s.replace("A.countP (fun a => (a == x) || t.contains a) := by\n      congr 1", "A.countP (fun a => (a == x) || t.contains a) := by\n      simp only [List.contains_cons]")
        for predicate in ("Near N L a b", "Covers N L a r"):
            keyword = predicate.split()[0]
            s = s.replace(f"    simp only [decide_eq_true_eq, {keyword}] at hn", f"    have hn' : {predicate} := of_decide_eq_true hn\n    unfold {keyword} at hn'")
        s = s.replace("if_true", "ite_true")
    else:
        s = s.replace("import Solidity.Hash.CollisionBound", "import tests.h62.item6.«migrate-hash».CollisionBound")
        for event, premise in (("eagerCollides", "CollisionFree"), ("eagerRegionsFail", "RegionsDisjoint")):
            s = s.replace(f"simp only [{event}, eagerQueries, decide_eq_true_eq, Classical.not_not]\n      exact {premise}.nil", f"simp only [{event}, eagerQueries]\n      exact fun h => (of_decide_eq_true h) {premise}.nil")
    (root/f"{name}.lean").write_text(s)
