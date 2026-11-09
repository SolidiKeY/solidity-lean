#!/usr/bin/env python3
"""Check source-role evidence and regressions; never a Lean validation gate."""
import argparse
import hashlib
import json
import pathlib
from semantic_inventory import classify, result_inputs

p=argparse.ArgumentParser(description=__doc__)
p.add_argument("--repo",type=pathlib.Path,required=True)
p.add_argument("--source",type=pathlib.Path,required=True)
p.add_argument("--semantic",type=pathlib.Path,required=True)
a=p.parse_args()
source=json.loads(a.source.read_text());ledger=json.loads(a.semantic.read_text())
assert hashlib.sha256(a.source.read_bytes()).hexdigest()==ledger["source_inventory_sha256"]
assert ledger["source_map_sha256"]==source["map_sha256"]
assert ledger["statement_count"]==len(ledger["statements"])==968
original={r["source_qualified_name"]:r for r in source["theorems"]}
assert len({r["name"] for r in ledger["statements"]})==968
assert set(original)=={r["name"] for r in ledger["statements"]}
for row in ledger["statements"]:
    old=original[row["name"]]
    assert row["signature_sha256"]==old["signature_sha256"]
    assert row["owner"]==old["owner"]
    assert len(row["explicit_binders"])==len(old["binder_evidence"])
    for b,prior in zip(row["explicit_binders"],old["binder_evidence"]):
        assert b["source"]==prior["source"] and b["domain_source"]==prior["domain_source"]
    for b in row["explicit_binders"]+row["context_binder_candidates"]+row["result_type_inputs"]:
        assert b["inhabitation"]=="unproved"
        assert b["semantic_status"]=="source-evidence; pending elaboration"
    assert row["simultaneous_witness"]=="pending"
    assert row["fidelity"]=="pending elaboration"
assert ledger["explicit_binder_count"]==sum(len(r["explicit_binders"]) for r in ledger["statements"])==6254
assert ledger["result_input_group_count"]==sum(len(r["result_type_inputs"]) for r in ledger["statements"])==28
assert len(ledger["result_resolution_queue"])==4
for fact in ledger["predicate_source_facts"]+[ledger["prop_structure_fact"]]:
    raw=(a.repo/fact["path"]).read_bytes();text=raw.decode()
    assert hashlib.sha256(raw).hexdigest()==fact["module_sha256"]
    assert text[fact["start"]:fact["end"]]==fact["header_source"]
    assert hashlib.sha256(fact["header_source"].encode()).hexdigest()==fact["header_sha256"]
fact=ledger["local_alias_fact"];raw=(a.repo/fact["path"]).read_bytes()
assert hashlib.sha256(raw).hexdigest()==fact["module_sha256"]
assert raw.decode()[fact["start"]:fact["end"]]==fact["source"]
# Protect the distinction motivating this stage: data functions, predicates,
# and universally quantified proof assumptions are different binder roles.
fixtures=[
    ("Nat → Nat","predicate-or-function-candidate","data-function"),
    ("Nat → Prop","predicate-or-function-candidate","predicate-family"),
    ("Nat → True","predicate-or-function-candidate","proof-assumption"),
    ("∀ (i : Nat), i = i","predicate-or-function-candidate","proof-assumption"),
    ("∀ (i : Nat), Nat","predicate-or-function-candidate","data-function"),
    ("∀ (i : Nat), Prop","predicate-or-function-candidate","predicate-family"),
    ("Prop","data-or-index-candidate","proposition-parameter"),
    ("Type","type-parameter","type-parameter"),
    ("Source.Val D (.int t)","data-or-index-candidate","data-input"),
    ("IntegerLocalFamily t si ti source target","indexed-certificate-or-map","proof-assumption"),
    ("ContextMap srcΓ Γ","indexed-certificate-or-map","indexed-certificate"),
    ("P8a.Producer S reference origins roots","global-producer-contract","global-contract"),
    ("t.lo ≤ x ∧ x ≤ t.hi","predicate-or-function-candidate","proof-assumption"),
    ("(Source.evalE G F n e).run s = out","predicate-or-function-candidate","proof-assumption"),
]
for expr,prior,expected in fixtures:
    assert classify(expr,prior)[0]==expected,(expr,classify(expr,prior))
# No dropping explicit producer assumptions because a proof body ignores them.
family_rows=[b for r in ledger["statements"] for b in r["explicit_binders"] if "IntegerLocalFamily" in (b["domain_source"] or "")]
assert len(family_rows)==64
assert all(b["kind"]=="proof-assumption" and b["role"]=="per-input-family-alignment" for b in family_rows)
producer_rows=[r for r in ledger["statements"] if any(b["kind"]=="global-contract" for b in r["explicit_binders"])]
assert len(producer_rows)==15
for suffix in ("scalar_value","source_assignment_run"):
    assert any(r["name"].endswith("."+suffix) for r in producer_rows)
print("PASS: all 968 identities/signature hashes preserved;6254 explicit groups;28 result input groups;4 untyped-result groups retained;source predicate facts verified;14 Prop/data/function regressions;15 producer assumptions retained")
print("NOT CHECKED: elaboration, constant resolution, inherited telescope membership, simultaneous witnesses, success/totality")
