#!/usr/bin/env python3
"""Frozen provisional Packing comparison; owner approval and TV coverage unclaimed."""
import argparse
import json
from pathlib import Path
from inventory import BASE
from pilot import module

HERE = Path(__file__).resolve().parent
PROTOTYPE = "9e8e83ae97b466c01e9306fb8b2246ded6469462"
PACKING = "Solidity/Yul/Views/Packing.lean"
ADDED = ["prototypes/" + name + ".lean" for name in
         ["TvYulBlock", "ViewsPackingBase", "ViewsPackingBridge", "ViewsPackingProgram", "ViewsPackingLaws"]]
ADDED += ["prototypes/shadow/" + PACKING]
CONSUMERS = ["Solidity/Yul/Views/" + name + ".lean" for name in ["Widths", "Regions"]]


def measure():
    before = module(BASE, PACKING)
    after = [module(PROTOTYPE, path) for path in ADDED]
    old = {s["name"]: s["signature"] for s in before["theorems"]}
    new = {s["name"]: s["signature"] for m in after for s in m["theorems"]}
    assert all(new.get(name) == signature for name, signature in old.items())
    consumers = [module(BASE, path) for path in CONSUMERS]
    for old_consumer in consumers:
        assert module(PROTOTYPE, old_consumer["path"])["sha256"] == old_consumer["sha256"]
    totals = {key: sum(m[key] for m in after) for key in ["physical_lines", "lexical_declarations"]}
    return dict(base=BASE, prototype_commit=PROTOTYPE, status="provisional_unapproved",
                covered_views_family=None, verdict=None,
                boundary="Packing only; two word proofs rederived, every other declaration retained. Shared existing library imports are excluded symmetrically; this is not a full import-closure size. All new checker, soundness/completeness, bridge, program, algebra and facade sources count.",
                technique_boundary="Restored word exports now consume checker-produced Artifact run equalities and decode their equal first stack words. BitVec identities and refinement lemmas remain necessary and counted. Each helper executes one read or write code on a mathematically prepared input, not a concatenated two-code run. No owner-approved TV family coverage or reduction is claimed.",
                before=before, after=dict(modules=after, **totals),
                statements_preserved=list(old), signatures_exact=True,
                consumers_unchanged=consumers,
                implemented_footprint=dict(mapped_functions=["Solidity.Yul.Views.Field.findWord", "Solidity.Yul.Views.Field.saveWord"], transferred_exports=["Solidity.Yul.Views.Field.find_saveWord", "Solidity.Yul.Views.Field.saveWord_unchanged"], retained_theorems=[name for name in old if name not in ["Solidity.Yul.Views.Field.find_saveWord", "Solidity.Yul.Views.Field.saveWord_unchanged"]], boundary="Packing is the sole family with explicit operation/Artifact mappings in this prototype. Widths/Regions are compatibility consumers. No mappings for typed storage/world writeback or arbitrary heterogeneous aggregate/byte geometry are implemented; their existing proofs are not deleted or given word-sized premises. This is an implemented footprint, not global impossibility or approved coverage."),
                largest_covered_family="Unestablished while owner-approved TV bridge/coverage is pending; Packing is a provisional candidate, not a largest-covered claim.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = measure()
    target = HERE / "views.json"
    if args.check:
        assert json.loads(target.read_text()) == result
        print("frozen provisional Packing inventory and all 11 exact signatures: PASS")
    else:
        target.write_text(json.dumps(result, indent=2) + "\n")
