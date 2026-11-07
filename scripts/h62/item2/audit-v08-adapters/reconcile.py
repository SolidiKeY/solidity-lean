#!/usr/bin/env python3
"""Reconcile separate limited acceptances without claiming a complete inventory."""
import argparse,json
from pathlib import Path

def require(condition, message):
    if not condition:
        raise ValueError(message)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for k in ["census","resource","local","out"]:ap.add_argument("--"+k,type=Path,required=True)
    a=ap.parse_args();c=json.loads(a.census.read_text());r=json.loads(a.resource.read_text());l=json.loads(a.local.read_text())
    require(c["summary"]["complete_interface_inventory"] is False, "Audit reconciliation predicate failed")
    require(r["status"]=="RESOURCE_FAMILY_ONLY_PASS" and l["status"]=="LOCAL_GUARD_ONLY_PASS", "Audit reconciliation predicate failed")
    rows=c["declarations"];indexed={x["id"]:x for x in rows};require(len(indexed)==len(rows), "Audit reconciliation predicate failed")
    covered={x["census_id"] for x in r["witnesses"]}
    local_names={x["target"] for x in l["reviewed"]}
    for row in rows:
        if row["name_candidate"] in local_names:
            require(row["id"] not in covered, "Audit reconciliation predicate failed");covered.add(row["id"])
    require(len(covered)==13 and covered<=set(indexed), "Audit reconciliation predicate failed")
    output=dict(status="PARTIAL_AUDIT",complete_interface_inventory=False,
        lexical_theorem_candidates=len(rows),accounted_source_theorems=13,
        ordinary_joint_witness_targets=6,intentional_H69_refutations=1,
        no_propositional_premise_source_theorems=6,
        additional_coherent_proof_fields=4,per_input_coherent_carriers=2,
        inhabited_resource_predicates=1,global_SourceSpec_producer_witnesses=0,
        remaining_lexical_theorems=len(rows)-len(covered),
        remaining_lexical_ids=[key for key in indexed if key not in covered],
        remaining_generated_local_candidates=l["remaining_generated_candidates"],
        limits=["Lexical count omits further structure proof fields and predicate definitions; full all-kind census remains pending.",
          "Global SourceSpec producer structures are not witnessed by per-input view/resource fixtures.",
          "Local guard success excludes both trivial compilers in its supported scope; charged gas/fork validation remains pending.",
          "All four original checkpoints and final full-root gates remain unfinished."])
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(output,sort_keys=True,indent=2)+"\n")
    print("PARTIAL_AUDIT: 13 source theorems accounted, 4 additional coherent proof fields, "+str(len(rows)-len(covered))+" lexical theorems plus further interface declarations pending")

if __name__=="__main__":main()
