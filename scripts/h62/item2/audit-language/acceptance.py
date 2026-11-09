#!/usr/bin/env python3
"""Independent lexical census reconciliation and confirmed-regression checks."""
import json
import re
from census import BASE, git, generate, mask, scan

report = generate()
assert not report["scan_errors"], report["scan_errors"]
assert not report["unresolved_references"], report["unresolved_references"]
expected = set()
for path in report["sources"]:
    source = git("show", f"{BASE}:{path}").decode()
    # Count commands without using scan's declaration regex/delimiter traversal.
    for m in re.finditer(r"(?m)^.*?\b(?:theorem|lemma)\s+([^\s({:\[]+)", mask(source)):
        expected.add((path, source.count("\n", 0, m.start()) + 1, m[1]))
actual = {(r["path"], r["line"], r["id"].split(":", 2)[2]) for r in report["declarations"]}
assert expected == actual, {"missed": sorted(expected-actual), "extra": sorted(actual-expected)}
assert len(actual) == len(report["declarations"])
by_name = {r["name_candidate"]: r for r in report["declarations"]}
for name in ("Solidity.Source.DataOK.mono", "Solidity.Source.exprNSAt_step",
             "Solidity.Fml.toBF_isSome", "Solidity.Idx.wk_refl"):
    assert name in by_name, name
for name in ("Solidity.Source.STy.eq_of_same", "Solidity.Thin.length_le"):
    assert "\ntheorem " not in by_name[name]["source_signature"], name
assert "where" not in by_name["Solidity.Source.exprNSAt_step"]["source_signature"]
fixture = b"""namespace N
variable {a : Nat}
mutual
@[simp] theorem a : True := True.intro
end
omit a in
theorem _root_.R.b (h : True := True.intro) : True
  | => h
end N
"""
r = scan("fixture.lean", fixture, {"fixture"})
assert [x["name_candidate"] for x in r] == ["N.a", "R.b"]
assert r[1]["source_signature"].endswith(": True")
assert "True.intro" in r[1]["source_signature"]
print(json.dumps({"status": "PASS-source-census-only", "files": len(report["sources"]),
                  "reconciled_declarations": len(actual), "kernel_certification": False}, sort_keys=True))
