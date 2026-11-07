#!/usr/bin/env python3
"""Join authored criteria with frozen census and hash-bound successful checks.
No source review, theorem name, or original proof reference counts as a check.
The dependency graph is a source import graph, not a kernel declaration graph.
"""
import argparse
import functools
import hashlib
import json
import pathlib
import re
import subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
ROOT = pathlib.Path(__file__).resolve().parents[4]
PLAN = ROOT/"tests/h62/item2/audit-roadmap"
BLOCKERS = {
    "Solidity/Hash/CollisionBound.lean": "DEP-HASH-01",
    "Solidity/SortCheck/Parser.lean": "DEP-PARSER-01",
    "Solidity/Syntax/Raw.lean": "DEP-RAW-01",
    "Solidity/Backend/Creation/Linking.lean": "DEP-LINKING-01",
}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

@functools.lru_cache(None)
def dependencies(path):
    p = ROOT/path
    if not p.exists():
        return frozenset([path])
    # Leaf external/builtin imports are retained by name; no proof about them.
    imports = re.findall(r"^import\s+(\S+)", p.read_text(), re.M)
    ds = [dependencies(("Bridge/" if m.startswith("SolidityBridge.") else "")+
          m.replace(".","/")+".lean") for m in imports]
    return frozenset([path]).union(*ds)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--census", required=True, type=pathlib.Path)
    ap.add_argument("--results", action="append", default=[], type=pathlib.Path)
    ap.add_argument("--output", required=True, type=pathlib.Path)
    args = ap.parse_args()
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError("H44: bulk report must remain off git")
    census = json.loads(args.census.read_text())
    assert census["base"] == BASE
    modules = {m["path"]:m for m in census["modules"]}
    for path, m in modules.items():
        assert sha(ROOT/path) == m["sha256"], f"frozen source changed: {path}"
    classification = json.loads((PLAN/"h69-classification.json").read_text())
    explicit = classification["explicit_false_controls"]
    refutations = classification["root_refutations"]
    rules = {r["name"]:r for r in explicit+refutations}
    assert len(rules) == 47 and len(explicit) == 3 and len(refutations) == 44
    rows = {r["source_qualified_name"]:r for r in census["statements"]}
    assert len(rows) == len(census["statements"])
    assert set(rules) <= set(rows)
    for r in explicit:
        assert rows[r["name"]]["signature"].endswith(": False")
    checked = {}
    result_sources = []
    for p in args.results:
        records = json.loads(p.read_text())
        # Failed/incomplete invocations do not supply accepted evidence.
        assert records and all(r["exit"] == 0 for r in records), p
        pin_path = pathlib.Path("/workspace/h62-coordinator-inputs/toolchain-pin.json")
        pin = json.loads(pin_path.read_text())
        for r in records:
            assert r["toolchain_pin_sha256"] == sha(pin_path), "stale toolchain pin"
            assert r["official_archive_sha256"] == pin["sha256"], "unverified official archive"
            assert r["compiler_sha256"] == sha(pathlib.Path(records[0]["command"][0])), "changed compiler"
        version = pathlib.Path(next(r["log"] for r in records if r["label"] == "lean-version")).read_text()
        assert "version " + pin["toolchain"].rsplit(":v",1)[1] in version
        for r in records:
            checked[r["label"]] = r
        result_sources.append(dict(path=str(p.resolve()), sha256=sha(p)))
    accepted = 0
    witnesses = json.loads((PLAN/"witness-index.json").read_text())["entries"]
    assert len({w["name"] for w in witnesses}) == len(witnesses)
    for w in witnesses:
        row = rows[w["name"]]
        original = checked.get(row["module"])
        helper = checked.get(w["helper_file"])
        if original is None or helper is None:
            continue
        for dep in dependencies(w["helper_file"]):
            if (ROOT/dep).is_file():
                assert dep in checked, f"missing checked dependency: {dep}"
                assert checked[dep]["source_sha256"] == sha(ROOT/dep), f"stale dependency: {dep}"
            else:
                assert dep.startswith(("Lean/", "Init/", "Std/")), f"untracked external dependency: {dep}"
        assert original["source_sha256"] == modules[row["module"]]["sha256"]
        assert helper["source_sha256"] == sha(ROOT/w["helper_file"])
        log = pathlib.Path(helper["log"]).read_text()
        assert "sorryAx" not in log and "error:" not in log
        assert f"'{w['helper']}' " in log
        axiom_lines = [line for line in log.splitlines() if line.startswith("'")]
        for line in axiom_lines:
            if "depends on axioms:" in line:
                names = line.split("[",1)[1].rstrip("]").split(", ")
                assert set(names) <= {"propext","Classical.choice","Quot.sound"}, line
        row["witness_status"] = "checked-joint-witness-or-closed-statement"
        row["witness"] = w["helper"]
        row["premise_world"] = w["premise_world"]
        row["check_log"] = helper["log"]
        row["checked_helper_sha256"] = helper["source_sha256"]
        accepted += 1
    for name, row in rows.items():
        rule = rules.get(name)
        row["classification"] = rule["criterion"] if rule else "ordinary-joint-witness-required"
        if rule:
            row["why_intentional"] = rule["why_intentional"]
            row["impossibility_proof_reference"] = rule["impossibility_proof"]
            row["impossibility_proof_status"] = "dependency-check-blocked"
        ds = dependencies(row["module"])
        row["dependency_blockers"] = sorted(BLOCKERS[p] for p in BLOCKERS if p in ds)
    census["summary"].update(witnessed=accepted, uncovered=len(rows)-accepted,
        h69_intentional_impossible=3, h69_impossibility_checked=0,
        root_refutations_requiring_outer_witness=44,
        source_signature_fidelity="let-expression delimiter fix; elaborated comparison pending")
    census["check_sources"] = result_sources
    census["h69"] = classification["authorization"]
    census["module_dependency_blockers"] = {
        path: sorted(BLOCKERS[p] for p in BLOCKERS if p in dependencies(path))
        for path in modules}
    out.mkdir(parents=True,exist_ok=True)
    data = (json.dumps(census,ensure_ascii=False,indent=2)+"\n").encode()
    (out/"audit-census.json").write_bytes(data)
    (out/"SHA256SUMS").write_text(hashlib.sha256(data).hexdigest()+"  audit-census.json\n")
    print(json.dumps(census["summary"],sort_keys=True))

if __name__ == "__main__":
    main()
