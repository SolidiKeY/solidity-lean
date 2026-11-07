#!/usr/bin/env python3
"""Acceptance for H70 area routing and known source-classification pitfalls."""
import copy
import importlib.util
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location("reconcile",ROOT/"scripts/h62/item2/audit-memory-operations/reconcile.py")
reconcile = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reconcile)

def classify(text,kind="theorem"):
    return reconcile.classify(dict(kind=kind,source_command_region=text))

let = "theorem letWitness (n : Nat) : let a := n; let b := a; b = n := by rfl"
r = classify(let)
assert r["header_source"].endswith("b = n ") and "by rfl" not in r["header_source"]
equation = "theorem byCases (n : Nat) : Nat → True\n | 0 => by trivial\n | n+1 => by trivial"
r = classify(equation)
assert "=>" not in r["header_source"] and "Nat → True" in r["header_source"]
ambiguous = "theorem ambiguous : (match 0 with\n | 0 => True\n | _ => False) := by trivial"
# A bracketed match is kept in the type, not mistaken for equation proof arms.
r = classify(ambiguous)
assert "match 0 with" in r["header_source"] and "by trivial" not in r["header_source"]
r = classify("theorem unresolved : match 0 with\n | 0 => True\n | _ => False := by trivial")
assert r["header_source"] == "" and r["header_end"] is None
assert "unresolved" in r["header_boundary_status"]

v1 = """structure Certificate where
  heap : StorageHeapCertificate value hm
  correct : ∀ (hp : Heap H), AllocatorRepr hp base frame cursor m → ∃ m', run code m = m'
"""
v2 = v1.replace("  correct", "  feasible : AllocatorWitness cost\n  correct")
carrier = """structure Witness where
  heap : Heap H
  machine : Machine
  represented : AllocatorRepr heap base frame cursor machine
  fits : cursor.val + cost < W
"""
assert classify(v1,"structure")["bundle"] == "global-uniform-obligation-bundle-candidate"
assert classify(v2,"structure")["bundle"] == "global-obligation-with-explicit-input-witness-candidate"
assert classify(carrier,"structure")["bundle"] == "per-input-data-and-predicate-carrier-candidate"
assert classify(v1,"structure")["fields"][1]["role"] == "universally-quantified-obligation-candidate"

source = json.loads(pathlib.Path('/workspace/h62-audit-memory-evidence/census.json').read_text())
routes = json.loads((ROOT/'tests/h62/item2/audit-memory-operations/owner-routes.json').read_text())
ownerpath = pathlib.Path('/workspace/h62-coordinator-inputs/ownership.json')
owners = json.loads(ownerpath.read_text())
result = reconcile.reconcile(ROOT,source,routes,owners,ownerpath)
assert [(r['path'],r['line'],r['name']) for r in result['declarations']] == [(r['path'],r['line'],r['name']) for r in source['declarations']]
assert [r['path'] for r in result['modules']] == [r['path'] for r in source['modules']]
assert result['counts']['area_routed_declarations'] == 4141
assert result['counts']['kernel_verified_signatures'] == 0
assert result['counts']['exact_live_file_owner_confirmations'] == 0
assert result['counts']['public_compiler_contract_credits'] == 0
rows = {r['name']:r for r in result['declarations'] if r['kind']=='structure'}
def keys(name): return [o['key'] for o in rows[name]['area_routing']['area_owners']]
assert keys('Solidity.Backend.AbiEntry.Premises.Statement') == ['V09']
assert keys('Solidity.Backend.AbiEntry.Premises.CopyAgreement') == ['V11']
assert keys('Solidity.Backend.MemoryCopies.LocationStepPremise') == ['V10','V11']
assert keys('Solidity.Backend.MemoryCopies.Panic41Premise') == ['MRS']
assert [o['key'] for o in rows['Solidity.Backend.MemoryCopies.Panic41Premise']['area_routing']['premise_dischargers']] == ['VY5']
assert [o['key'] for o in rows['Solidity.Backend.AbiEntry.Premises.V11G34_ViewCoherence']['area_routing']['premise_dischargers']] == ['V13']
assert rows['Solidity.Backend.MemoryCopies.V2.StorageWordCertificate']['premise_bundle']['bundle'] == 'global-obligation-with-explicit-input-witness-candidate'
assert rows['Solidity.Backend.MemoryCopies.V2.AllocatorWitness']['premise_bundle']['bundle'] == 'per-input-data-and-predicate-carrier-candidate'
for row in result['declarations']:
    bundle = row['premise_bundle']
    for field in bundle['fields']:
        assert row['source_command_region'][field['start']:field['end']] == field['source']
    for binder in bundle['binders']:
        assert bundle['header_source'][binder['start']:binder['end']] == binder['source']
    assert row['status']=='unverified'
    assert row['area_routing']['edit_authorization']=='none outside original audit scope'

for problem in ('missing-route','ambiguous-route','bad-evidence','frozen-hash'):
    badroutes,badsource=copy.deepcopy(routes),copy.deepcopy(source)
    if problem=='missing-route': badroutes['rules']=[]
    if problem=='ambiguous-route': badroutes['rules'].append(dict(badroutes['rules'][0],id='duplicate'))
    if problem=='bad-evidence': badroutes['rules'][0]['evidence'][0]['contains']='THIS EVIDENCE DOES NOT EXIST'
    if problem=='frozen-hash': badsource['modules'][0]['sha256']='0'*64
    try: reconcile.reconcile(ROOT,badsource,badroutes,owners,ownerpath)
    except ValueError: pass
    else: raise AssertionError('failed open: '+problem)
findings=json.loads((ROOT/'tests/h62/item2/audit-memory-operations/source-findings.json').read_text())
reconcile.attach_findings(ROOT,result,findings)
assert result['counts']['escalation_statements']==1
assert result['source_findings'][0]['qualified_statement']=='Solidity.Backend.MemoryCopies.StorageWordCertificate.correct'
bad=copy.deepcopy(findings)
bad['findings'].append(copy.deepcopy(bad['findings'][0]))
try: reconcile.attach_findings(ROOT,result,bad)
except ValueError: pass
else: raise AssertionError('duplicate escalation admitted')
print('PASS: all source identities and spans, let/equation/match boundaries, global-vs-input distinction, mixed owner/caller routes, fail-closed evidence/hash checks; zero public credits')
