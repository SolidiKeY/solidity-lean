#!/usr/bin/env python3
"""Frozen Packing comparison on the H299-approved operation-bridge basis; no reduction acceptance."""
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
    return dict(base=BASE, prototype_commit=PROTOTYPE, status="basis_approved_validation_pending",
                basis_authorization="H299 A: operation bridge approved as pilot basis, conditional on exact export restoration, retained Nat accounting, Views comparison and ordinary validation; no family-reduction acceptance.",
                selected_family="Solidity.Yul.Views.Packing", family_reduction_accepted=False,
                covered_views_family=None, verdict="NO-GO",
                boundary="Packing only; two word proofs rederived, every other declaration retained. Shared existing library imports are excluded symmetrically; this is not a full import-closure size. All new checker, soundness/completeness, bridge, program, algebra and facade sources count.",
                technique_boundary="Restored word exports now consume checker-produced Artifact run equalities and decode their equal first stack words. BitVec identities and refinement lemmas remain necessary and counted. Each helper executes one read or write code on a mathematically prepared input, not a concatenated two-code run. H299 approves this operation bridge as the pilot basis; no broader family coverage or reduction acceptance is claimed.",
                before=before, after=dict(modules=after, **totals),
                statements_preserved=list(old), signatures_exact=True,
                consumers_unchanged=consumers,
                implemented_footprint=dict(mapped_functions=["Solidity.Yul.Views.Field.findWord", "Solidity.Yul.Views.Field.saveWord"], transferred_exports=["Solidity.Yul.Views.Field.find_saveWord", "Solidity.Yul.Views.Field.saveWord_unchanged"], retained_theorems=[name for name in old if name not in ["Solidity.Yul.Views.Field.find_saveWord", "Solidity.Yul.Views.Field.saveWord_unchanged"]], boundary="Packing is the sole family with explicit operation/Artifact mappings in this prototype. Widths/Regions are compatibility consumers. No mappings for typed storage/world writeback or arbitrary heterogeneous aggregate/byte geometry are implemented; their existing proofs are not deleted or given word-sized premises. This is the sole explicitly mapped family in this prototype, not a global impossibility result or family-reduction acceptance."),
                largest_covered_family="Packing is the sole existing Views family with explicit mappings in this implemented operation bridge. Its two word exports are transferred; nine other theorem exports are retained. No broader typed-state or aggregate coverage or family-reduction acceptance.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = measure()
    target = HERE / "views.json"
    if args.check:
        assert json.loads(target.read_text()) == result
        print("frozen H299-basis Packing inventory and all 11 exact signatures: PASS")
    else:
        target.write_text(json.dumps(result, indent=2) + "\n")
