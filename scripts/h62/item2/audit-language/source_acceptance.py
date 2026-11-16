#!/usr/bin/env python3
"""Guard fresh source recovery against omitted declarations or forged proof credit.

This separate H151 source-only check never substitutes for historical ownership
acceptance. Recompute the frozen report, independently reconcile lexical command
identities with a separate command regex (shared comment/string masking), and
preserve explicit no-owner/no-kernel/no-witness boundaries.
"""
import argparse
import json
import re
from pathlib import Path
from census import BASE, git, mask, scan
from source_only import generate


def validate(report, expected):
    if report != expected:
        raise ValueError("fresh report differs from frozen source recovery")
    if report["historical_replay"] or report["kernel_checked"] or report["certified_witnesses"]:
        raise ValueError("source recovery cannot grant replay or proof credit")
    ids = [r["id"] for r in report["declarations"]]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate source declaration identity")
    if any(r["owner"] is not None or r["owner_status"] != "UNVERIFIABLE-historical-snapshot"
           for r in report["declarations"]):
        raise ValueError("historical owner substitution")


def reconcile(report):
    expected = set()
    for path in report["sources"]:
        source = git("show", f"{BASE}:{path}").decode()
        for match in re.finditer(r"(?m)^.*?\b(?:theorem|lemma)\s+([^\s({:\[]+)", mask(source)):
            expected.add((path, source.count("\n", 0, match.start()) + 1, match[1]))
    actual = {(r["path"], r["line"], r["id"].split(":", 2)[2])
              for r in report["declarations"]}
    if expected != actual or len(actual) != len(report["declarations"]):
        raise ValueError("independent lexical command census mismatch")
    by_name = {r["name_candidate"]: r for r in report["declarations"]}
    for name in ("Solidity.Source.DataOK.mono", "Solidity.Source.exprNSAt_step",
                 "Solidity.Fml.toBF_isSome", "Solidity.Idx.wk_refl"):
        if name not in by_name:
            raise ValueError("known command omitted: " + name)
    for name in ("Solidity.Source.STy.eq_of_same", "Solidity.Thin.length_le"):
        if "\ntheorem " in by_name[name]["source_signature"]:
            raise ValueError("adjacent theorem swallowed: " + name)
    if "where" in by_name["Solidity.Source.exprNSAt_step"]["source_signature"]:
        raise ValueError("recursive proof boundary included in signature")
    return len(actual)


def parser_regressions():
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
    rows = scan("fixture", fixture, {"fixture"})
    if [r["name_candidate"] for r in rows] != ["N.a", "R.b"]:
        raise ValueError("namespace/mutual declaration regression")
    if not rows[1]["source_signature"].endswith(": True") or "True.intro" not in rows[1]["source_signature"]:
        raise ValueError("default-argument/equation proof boundary regression")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", type=Path, required=True)
    args = parser.parse_args()
    report = json.loads(args.census.read_text())
    validate(report, generate())
    count = reconcile(report)
    parser_regressions()
    print(json.dumps({"status": "PASS-fresh-source-only", "files": len(report["sources"]),
                      "reconciled_candidates": count, "historical_replay": False,
                      "kernel_checked": False, "certified_witnesses": 0}, sort_keys=True))


if __name__ == "__main__":
    main()
