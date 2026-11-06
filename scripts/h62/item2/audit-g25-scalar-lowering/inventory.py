#!/usr/bin/env python3
"""Join exact frozen source/kernel signatures with explicit premise roles.

Inventory establishes no inhabitance: a full checked joint witness is required.
"""
import argparse
import collections
import json
from pathlib import Path
import census

S="Solidity.Backend.Scalar."
E="Solidity.Backend.Environment."
GLOBAL={S+n for n in ["UnaryCertificate","BinaryCertificate","CheckedCertificate","ClosedCertificate","CheckedUnaryCertificate","ModularCertificate"]}
PER_INPUT={S+n for n in ["BinaryInvocation","CheckedInvocation","ClosedInvocation","SignedPowerInvocation"]}|{E+n for n in ["Represents","Stable","HashInput","NamespaceInput"]}
STATE_SPECIFIC={E+n for n in ["ValueCertificate","ValuesCertificate"]}


def classify(binder):
    head=binder["type_head"]
    if head in GLOBAL: return "global-uniform-premise-structure"
    if head in PER_INPUT: return "per-input-feasibility-structure"
    if head in STATE_SPECIFIC: return "state-specific-certificate-with-uniform-target-tail"
    if binder["is_proposition"]:
        if head=="[anonymous]" and binder["type"].startswith("∀"): return "global-function-law"
        return "per-input-logical-premise"
    if binder["instance_implicit"]: return "instance-data"
    return "intrinsic-input-data"


def build(source,kernel,schemas):
    public=[r for r in source["theorems"] if r["visibility"]=="public"]
    originals={r["name"]:r for r in public}
    typed={r["name"]:r for r in kernel}
    if len(originals)!=len(public) or len(typed)!=len(kernel): raise ValueError("duplicate inventory names")
    if set(originals)!=set(typed): raise ValueError("kernel/source statement sets differ")
    schema_map={r["name"]:r for r in schemas}
    if len(schema_map)!=len(schemas) or set(schema_map)!=GLOBAL|PER_INPUT|STATE_SPECIFIC:
        raise ValueError("premise structure schema census differs")
    rows=[]
    for name,original in originals.items():
        row=typed[name]
        if row["level_parameters"]: raise ValueError("polymorphic source telescope needs review")
        binders=[dict(b,role=classify(b)) for b in row["binders"]]
        roles=collections.Counter(b["role"] for b in binders)
        rows.append(dict(original,kernel_type=row["kernel_type"],kernel_type_sha256=census.digest(row["kernel_type"].encode()),
                         pretty_type=row["pretty_type"],conclusion=row["conclusion"],binders=binders,
                         premise_roles=dict(roles),binder_count=row["binder_count"],
                         has_global_model=bool(roles["global-uniform-premise-structure"] or roles["global-function-law"]),
                         has_per_input_feasibility=bool(roles["per-input-feasibility-structure"] or roles["per-input-logical-premise"]),
                         inhabitance_status="requires-checked-joint-witness"))
    counts=collections.Counter(b["role"] for row in rows for b in row["binders"])
    return {"base":source["base"],"public_statement_count":len(rows),"private_helper_count":source["summary"]["private_theorems"],
            "module_count":len(source["modules"]),"binder_role_counts":dict(counts),
            "global_model_statements":sum(row["has_global_model"] for row in rows),
            "per_input_feasibility_statements":sum(row["has_per_input_feasibility"] for row in rows),
            "premise_schemas":[dict(row,role=("global-uniform-premise-structure" if row["name"] in GLOBAL else "per-input-feasibility-structure" if row["name"] in PER_INPUT else "state-specific-certificate-with-uniform-target-tail")) for row in schemas],
            "statements":rows,"proof_boundary":"Classification only. Individual premise inhabitance is never joint-witness credit."}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ["source","kernel","schemas","output"]: p.add_argument("--"+name,type=Path,required=True)
    a=p.parse_args()
    report=build(json.loads(a.source.read_text()),json.loads(a.kernel.read_text()),json.loads(a.schemas.read_text()))
    a.output.write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k not in ["statements","premise_schemas"]},ensure_ascii=False,sort_keys=True))
    print("inventory_sha256="+census.digest(a.output.read_bytes()))
if __name__=="__main__": main()
