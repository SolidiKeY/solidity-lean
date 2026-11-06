#!/usr/bin/env python3
"""Explicit reviewed binder roles for witnessed statements only.
Never infer live ownership or classify uncovered declarations by name alone.
classify() is called inside acceptance's writer lock; main locks standalone use.
"""
import fcntl
import hashlib
import json
from pathlib import Path

EVIDENCE = Path("/workspace/h62-audit-typing-evidence/v4.24.0")
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
GROUPS = {
    "ClosureWitnesses": ({"α"}, set()),
    "ValuesListsWitnesses": ({"κ", "α"}, set()),
    "ValuesDefaultsWitnesses": ({"P"}, {"harr", "hfix", "hmap"}),
    "UnitsSuccess": (set(), set()),
    "ValuesHeredWitnesses": ({"P", "Q", "G", "B"}, {"hm", "hB"}),
    "ValuesOpsWitnesses": ({"P"}, {"hs", "hd", "hov"}),
}
EXPECTED = dict(ClosureWitnesses=23, ValuesListsWitnesses=9,
    ValuesDefaultsWitnesses=6, UnitsSuccess=1, ValuesHeredWitnesses=10, ValuesOpsWitnesses=9)

def classify():
    census = json.loads((EVIDENCE/"statement-census.json").read_text())
    assert census["base"] == BASE
    covered = [r for r in census["declarations"] if r["witness"]]
    assert len(covered) == len({r["name"] for r in covered}) == 58
    counts = {name: 0 for name in GROUPS}
    output = []
    for row in covered:
        prefix = "H62.AuditTyping."
        assert row["witness"].startswith(prefix)
        group = row["witness"].removeprefix(prefix).split(".")[0]
        assert group in GROUPS
        counts[group] += 1
        globals_, capabilities = GROUPS[group]
        binders = []
        for index, binder in enumerate(row["binders"]):
            eq_instance = group in {"ClosureWitnesses", "ValuesListsWitnesses"} and "`DecidableEq " in binder["typeExpr"]
            if binder["name"] in globals_:
                role = "global-parameter"
            elif binder["name"] in capabilities or eq_instance:
                role = "global-capability"
            else:
                role = "per-input-hypothesis" if binder["isProp"] else "per-input-data"
            binders.append(dict(index=index, name=binder["name"], isProp=binder["isProp"], role=role))
        assert len(binders) == len(row["binders"])
        digest = hashlib.sha256(json.dumps([row["typeExpr"], row["levelParams"]], sort_keys=True).encode()).hexdigest()
        output.append(dict(name=row["name"], source_path=row["source_path"], owner=None,
            owner_status=row["owner_status"], closed_signature_sha256=digest,
            simultaneous_input_witness=row["witness"], binders=binders,
            carrier_evidence="Bool specialization and synthesized equality instance where present" if group in {"ClosureWitnesses", "ValuesListsWitnesses"} else "full existential input telescope"))
    assert counts == EXPECTED
    assert sum(r["role"] == "global-capability" for row in output for r in row["binders"]) > 0
    result = dict(base=BASE, statements=len(output), binder_count=sum(len(r["binders"]) for r in output),
        groups=counts, declarations=output,
        limitations=["Roles are reviewed only for the witnessed whitelist.",
            "Global inhabitation alone never certifies per-input feasibility.",
            "Anonymous repeated binder names remain distinct by index.",
            "Live owners remain unresolved; no extra premise is added."])
    (EVIDENCE/"hypothesis-roles.json").write_text(json.dumps(result, sort_keys=True, indent=2)+"\n")
    baseline_path = EVIDENCE/"statement-census-first.json"
    assert baseline_path.exists(), "Historical signature baseline required"
    baseline = json.loads(baseline_path.read_text())
    assert baseline["base"] == BASE
    def signatures(value):
        return sorted((r["name"], r["typeExpr"], r["levelParams"]) for r in value["declarations"])
    original = signatures(baseline)
    current = signatures(census)
    assert original == current, "Frozen closed signature projection changed"
    canonical = json.dumps(current, ensure_ascii=False, sort_keys=True).encode("utf-8")
    fidelity = dict(base=BASE, constants=len(current), changed=[], equal=True,
        sha256=hashlib.sha256(canonical).hexdigest(),
        canonicalization="UTF-8 of json.dumps(sorted((name,typeExpr,levelParams) for every declaration), ensure_ascii=False, sort_keys=True), default separators; no trailing newline")
    (EVIDENCE/"closed-signature-fidelity.json").write_text(json.dumps(fidelity, sort_keys=True, indent=2)+"\n")
    print(f"Reviewed roles: {len(output)} statements, {result['binder_count']} binders")

def main():
    lockpath = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    lockpath.parent.mkdir(exist_ok=True)
    with lockpath.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        classify()

if __name__ == "__main__":
    main()
