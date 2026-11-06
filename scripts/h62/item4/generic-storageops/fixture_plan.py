#!/usr/bin/env python3
"""Exhaustive proof-work plan, NOT typed Lean fixtures or proved equivalence.
Whole control claims remain independent obligations until exact instances check.
"""
import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("classification",HERE/"classify.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
PIN=m.c.ROOT/"tests/h62/item4/generic-storageops/fixture-plan-manifest.json"

STRATEGIES={
"intrinsic-graph":"Prove on existing typed Value/Slot/Path operations by structural induction or operation equations; retain retained/live and Option outcomes separately.",
"mixed-control-clients":"Separate graph law from finite-region numeric transport; compose only through existing bridges with all original premises.",
"numeric-access-and-traces":"Prove generated-access/write-log law under unchanged FiniteRun/Transport bounds; preserve captured versus current reads and exact log order.",
"represented-composition":"Derive intermediate owner/transport from actual operation; preserve every original selected query and outside frame, never assume desired postowner.",
"structured-target":"Prove actual existing instruction/loop execution with full Machine context; preserve checks and failure outcomes, no Source/world inference.",
"represented-target-adapter":"Prove actual target execution then compose existing Represented/Transport facts; retain coverage and local region premises.",
"published-compiler-fragment":"Retain admission/refusal separately from runtime outcomes; instantiate existing published compiler soundness at unchanged syntax and source states.",
"reached-endpoint":"Inhabit the same Path/State/ReachedEndpoint fields and actual execution; do not generalize a local witness into a universal Producer."
}

def build(classification):
    cases=[r for r in classification["declarations"] if r["role"] in ("public-control-claim","private-control-claim")]
    by_file={}
    for r in classification["declarations"]:by_file.setdefault(r["path"],[]).append(r)
    rows=[];packets=[]
    for path in sorted({r["path"] for r in cases}):
        originals=by_file[path]
        fixtures=[r for r in originals if r["role"]=="control-fixture-or-adapter"]
        claims=[r for r in originals if r in cases]
        # Whole module support is conservative retention, not a resolved dependency graph.
        packets.append(dict(path=path,claim_ids=[r["id"] for r in claims],
            fixture_ids=[r["id"] for r in fixtures],support_policy="retain-all-module-fixtures; cross-module imports remain pinned by original source hashes"))
        for r in claims:
            rows.append(dict(id=r["id"],name=r["name"],path=path,private=r["private"],
                status="unproved-await-dependency-and-owner-gates",
                formal_parameters=r["formal_parameters"],ambient_binders=r["ambient_binders"],
                exact_result_type=r["result_type"],source_hashes=r["source_hashes"],
                input_regime=r["input_regime"],strategy=STRATEGIES[r["domain"]],
                fixture_packet=path,
                equivalence=dict(candidate_source_template=r["source_template_sha256"],
                    permission="none",proved=False,
                    rule="source templates do not establish resolved type or semantic equivalence; retain singleton obligation until generic law and exact instance compile"),
                obligations=["Rebuild unchanged prerequisites with pinned official toolchain and KeySort before proof gates.",
                    "Express fixture inputs with original dependent Schema/Ty/Value/Path/Query/Machine types and original binder context; do not erase indices.",
                    "Prove parameterized operation law independently of expected fixture outputs; no decide-table semantic substitute.",
                    "Instantiate to EXACT original whole result type; preserve all conjunctions, tuple/list order, local lets, runtime quantifiers and hypotheses.",
                    "Retain negative/refusal and unavailable-observation distinctions; no refusal conclusion from mere nested none.",
                    "Check original and instance axiom sets without new sorry/axiom/native_decide or raised proof budgets.",
                    "Obtain exact-file owner agreement before originals/registration; owner applies any migration patch.",
                    "Measure original and proposed instance under identical tree/cache/resources; stop if slowdown exceeds10percent."],
                retained_contract_shapes=r["contract_shape"]))
    return dict(format=1,base=m.c.BASE,classification_sha256=m.c.digest(json.dumps(classification,ensure_ascii=False,indent=2)+"\n"),
        boundary="Work plan only; no Lean fixture/lemma/equivalence/correspondence has been proved or migrated.",
        totals=dict(claims=len(rows),packets=len(packets),private=sum(r["private"] for r in rows),public=sum(not r["private"] for r in rows)),
        packets=packets,cases=rows)

def validate(plan,classification):
    expected={r["id"]:r for r in classification["declarations"] if r["role"] in ("public-control-claim","private-control-claim")}
    actual={r["id"]:r for r in plan["cases"]}
    if len(actual)!=len(plan["cases"]) or set(actual)!=set(expected):raise ValueError("case omission/duplication")
    packets={p["path"]:p for p in plan["packets"]}
    if len(packets)!=len(plan["packets"]):raise ValueError("duplicate packet")
    for key,r in actual.items():
        old=expected[key]
        for a,b in (("source_hashes","source_hashes"),("formal_parameters","formal_parameters"),("ambient_binders","ambient_binders"),("exact_result_type","result_type"),("retained_contract_shapes","contract_shape")):
            if r[a]!=old[b]:raise ValueError("contract drift "+key)
        if r["equivalence"]["proved"] or r["equivalence"]["permission"]!="none":raise ValueError("unproved permission/equivalence claim")
        if r["id"] not in packets[r["fixture_packet"]]["claim_ids"]:raise ValueError("lost packet claim")
    for path,p in packets.items():
        want={r["id"] for r in expected.values() if r["path"]==path}
        if len(p["claim_ids"])!=len(set(p["claim_ids"])) or set(p["claim_ids"])!=want:raise ValueError("packet case coverage")
        want={r["id"] for r in classification["declarations"] if r["path"]==path and r["role"]=="control-fixture-or-adapter"}
        if len(p["fixture_ids"])!=len(set(p["fixture_ids"])) or set(p["fixture_ids"])!=want:raise ValueError("fixture support loss")

def main():
    p=argparse.ArgumentParser();p.add_argument("--output",type=Path,required=True);p.add_argument("--write",action="store_true");a=p.parse_args()
    if a.output.resolve().is_relative_to(m.c.ROOT):p.error("bulk output must be off git")
    classification=m.classify();m.validate(classification,m.c.census())
    expected=json.loads(m.MANIFEST.read_text())["classification_sha256"]
    if m.c.digest(json.dumps(classification,ensure_ascii=False,indent=2)+"\n")!=expected:raise SystemExit("classification pin drift")
    plan=build(classification);validate(plan,classification)
    text=json.dumps(plan,ensure_ascii=False,indent=2)+"\n"
    pin=json.dumps(dict(format=1,classification_sha256=expected,plan_sha256=m.c.digest(text),totals=plan["totals"]),indent=2)+"\n"
    if a.write:PIN.write_text(pin)
    elif PIN.read_text()!=pin:raise SystemExit("plan pin drift")
    a.output.write_text(text)
    print("FIXTURE_PLAN_COVERAGE_PASS "+json.dumps(plan["totals"],sort_keys=True))
    print("plan_sha256="+m.c.digest(text))
    print(plan["boundary"])

if __name__=="__main__":main()
