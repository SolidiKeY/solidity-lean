#!/usr/bin/env python3
"""All11 reachable-mode telescopes; anonymous hypotheses are classified by occurrence.
Original private identity and typed/source/owner provenance remain frozen.
"""
import argparse,hashlib,json,subprocess
from pathlib import Path
from census import ROOT,BASE,scan
from input_roles import digest,SPECS as BRIDGE_OUTCOME
from mutability_input_roles import SPECS as CLOSER_PAYABLE
from assignable_input_roles import SPECS as ASSIGNABLE
from pure_input_roles import SPECS as PURE
from path_input_roles import SPECS as PATHS
from mirror_input_roles import SPECS as MIRRORS
from clean_tail_input_roles import SPECS as CLEAN_TAIL
from indexed_roles import annotate_occurrences
import verify_census as v
FILE="Solidity/Theory/Reachable/Mode.lean"
NOTES=[
    'No logical premise occurs: C/D/A are configuration/type data and phi is a formula value. The packet supplies all inputs at one configuration; an identity between validity readings is not itself program admission or a proof that every formula is valid.',
    'M is interface DATA with programs and allowance predicates, not an inhabited global correctness proof. The identity theorem has no EntryState hypothesis. The packet adds a genuine admitted entry as support, with inhabited Unit domains and an actual successful flag-writing interface; this support is not a new public premise.',
    'h quantifies EVERY compatible typed state for this FIXED formula under any mode, not only one reachable state and not every formula. A universally valid truth formula supplies that full law; independent real-entry evidence prevents an empty reachable interface from substituting for feasibility. No compiler claim follows.',
    'I is predicate DATA, not itself a proof that any world satisfies it. hI is the invariant over EVERY world reachable through this SAME fixed M. entry is the WHOLE law over world/transaction/action/state under invariant, acceptance, refusal=false, allowance and successful-entry conditions. h is validity of J-implies-phi at EVERY compatible typed state. The packet uses nontrivial CleanWorld/cleanTail and a real admitted entry, with all laws together.',
    'hI is the global invariant of the SAME M/I; sigma occurs AFTER it and remains data. The later h is one selected admitted reachable EntryState, not a premise that all typed states are reachable. The packet uses CleanWorld and an actual constructor/entry, rather than separately inhabited invariant and state structures.',
    'h is one selected EntryState, carrying a correlated reachable world, accepted transaction/action, payment guard, allowance and successful entry. Configuration and selected state coexist; default-storage data alone is not reachability. The packet also observes an actual declared flag.',
    'Private reset_ofState has only C/Gamma/sigma DATA inputs, no logical premise. The exact frozen elaborated PRIVATE identity remains pinned. Its packet selects a populated transient/persistent store and checks triple-versus-single reset through public idempotence; no visibility change or invented hypothesis occurs.',
    'J is persistent-formula STRUCTURE data including its universal reads law over the SAME pair of states when reset storages agree. h is satisfaction at this selected sigma, not universal validity. The chosen truth formula is disclosed as such; source setter success and actual entry are independent support, not inferred compiler coverage.',
    'The same persistent reads structure J coexists with a world fact hs and the selected successful entry equation en. World, transaction and resulting sigma are correlated. Global reads-law inhabitation alone does not provide this success; a real accepted zero-value entry supplies it.',
    'deploy quantifies EVERY constructor argument/transaction admitted by allowDeploy for the fixed M/J; it is a BOX over the constructor BODY, not a promise that payment guards admit every deployment. calls quantifies EVERY action and EVERY compatible typed state satisfying J, not one test execution. Box laws include the no-panic condition. The packet proves source setter success independently and supplies real entry; no target ABI/gas/compiler totality is claimed.',
    'Both whole constructor/body and action/all-state box obligations are preserved for the SAME M/J, plus global validity of J-implies-phi for the fixed phi. Persistent reads-law structure and selected formulas are data, not extra assumptions about all interfaces/formulas. Truth-formula inputs are explicit; actual source deployment/entry/write support is provided independently.',
]
ROWS=[
    ('Solidity.Reachable.validStart_any', 'C D A φ', [0, 1, 2], {}, 0, '20ae2d1af78320ccd505aef9562f753d9caa05ca09747b48f5a12ea341811a4e', '10c22365df559408e82770d128d32cd6bf46544eeec7b05f739d77f67d472ec3', 'Solidity.Reachable.validStart_any'),
    ('Solidity.Reachable.validStart_reachable', 'C D A M φ', [0, 1, 2], {}, 1, '761aeb5273123311f98100c65397130284931c956fb2fc7c1e92f30a818ba15d', '8afc88e839f7216816e4e4211961dbc909575932f01e5a1a064ea94f6059b38e', 'Solidity.Reachable.validStart_reachable'),
    ('Solidity.Reachable.ValidStart.reachable_of_any', 'C D A M φ h', [0, 1, 2], {5: 'all-compatible-states-validity-for-fixed-formula'}, 2, '678b18c9c4c22e23e40c2e382dd688f2ea5c8f21816f6280d84e23936c024a44', '5ed9c3c3de27dbf742be74f249eca3a86cebe62473a97a9d48c6534b36bac3f3', 'Solidity.Reachable.ValidStart.reachable_of_any'),
    ('Solidity.Reachable.ValidStart.of_invariant', 'C D A M I J φ hI entry h', [0, 1, 2], {7: 'all-reachable-worlds-invariant-for-fixed-interface-predicate', 8: 'all-conditional-entry-tuples-for-fixed-interface-predicate-formula', 9: 'all-compatible-states-valid-implication-for-fixed-formulas'}, 3, '186884119eb5fea9589dfbed9775070b631d54959b01bc66066751eb84195961', '811ed1b85bc58b5e964e5b002bcc93e1c9240cc977f722ba4c2903f12915846c', 'Solidity.Reachable.ValidStart.of_invariant'),
    ('Solidity.Reachable.EntryState.invariant', 'C D A M I hI σ h', [0, 1, 2], {5: 'all-reachable-worlds-invariant-for-fixed-interface-predicate', 7: 'per-input-selected-reachable-admitted-entry'}, 4, 'b76d13cae1d930da45c467672caeffcc5a76f42e78736f9ebfd4df0af91b0a57', '60937a12aa33ac132508c5326593a7ba5e4642c389da767ce4e066c3c4115358', 'Solidity.Reachable.EntryState.invariant'),
    ('Solidity.Reachable.EntryState.storage', 'C D A M σ h', [0, 1, 2], {5: 'per-input-selected-reachable-admitted-entry'}, 5, 'b9ce01a5827cfe39d8498d8551b3d6ef6cd15881ec66a6fcb4120353b67c4d63', 'de23ed48255de89b531df4559daa30b7b7f7da48ab7a6b69ac1e8c7dd7c6bf83', 'Solidity.Reachable.EntryState.storage'),
    ('Solidity.Reachable.reset_ofState', 'C Γ σ', [0, 1], {}, 6, '7124d10ebbdc8d6ba4f09fd109aaef41225cba235a0b221f20bf5f9b2ba6b257', '0fd803139debf7c68e96c50200d4faf8107ef5293aa30b35e1ee4bec89384814', '_private.Solidity.Theory.Reachable.Mode.0.Solidity.Reachable.reset_ofState'),
    ('Solidity.Reachable.PersistentFml.at_ofState', 'C J σ h', [0], {3: 'per-input-selected-state-formula-satisfaction'}, 7, 'fe2c007a9ae236f7bd0df1467bdf3b61359ce8cc9dd0b736d8fd3e80700df0f7', 'deaec218f4e18fe62f3dfa7802bdd4d596e93b78ca6bfbbada175d4ee9bd591a', 'Solidity.Reachable.PersistentFml.at_ofState'),
    ('Solidity.Reachable.PersistentFml.at_enter', 'C J s tx σ hs en', [0], {5: 'per-input-selected-world-observation-satisfaction', 6: 'per-input-selected-successful-entry-equation'}, 8, '755cf9dba306dbbe0fe06ffe99f3539f375d867b9aa58f397e70405b1044868c', '8981ab62ce5c8f6e25b72faafb3b51379f59ee4a92418cf6d7e012c7dab1274e', 'Solidity.Reachable.PersistentFml.at_enter'),
    ('Solidity.Reachable.PersistentFml.invariant', 'C D A M J deploy calls', [0, 1, 2], {5: 'all-allowed-constructor-inputs-and-transactions-body-box-law', 6: 'all-actions-and-compatible-states-call-body-box-law'}, 9, '7e351e01940d8c7551bf73e28da34d071caede0d8caa27f6ca970e889cb896da', '995c90d544723df0bfdeb79ba24c48e90436f4524c3b29f8f3da4ab31f7b59db', 'Solidity.Reachable.PersistentFml.invariant'),
    ('Solidity.Reachable.ValidStart.of_persistent', 'C D A M J φ deploy calls h', [0, 1, 2], {6: 'all-allowed-constructor-inputs-and-transactions-body-box-law', 7: 'all-actions-and-compatible-states-call-body-box-law', 8: 'all-compatible-states-valid-implication-for-fixed-formulas'}, 10, 'eae33408f67c9caaffa2c5d754dc81a2a6253c0bc2ae1d7242827340788c1f24', 'e2883050fb1994c9f09c0a92a14245dd7f91c5eed1df41b32545789fab788671', 'Solidity.Reachable.ValidStart.of_persistent'),
]
SPECS={n:dict(binders=bs.split(),configuration=cfg,premises=props,notes=NOTES[note]) for n,bs,cfg,props,note,_,_,_ in ROWS}
PINS={n:dict(type_expr=ty,binders=bs,elaborated_name=full) for n,_,_,_,_,ty,bs,full in ROWS}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ("proof-evidence","historical-evidence","out"):ap.add_argument("--"+name,type=Path,required=True)
    a=ap.parse_args();proof=a.proof_evidence.resolve();old=a.historical_evidence.resolve();out=a.out.resolve()
    if any(p.is_relative_to(ROOT) for p in (proof,old,out)):raise SystemExit("Use off-Git evidence")
    source=old/"verified-census.json";manifest=dict(line.split("  ",1)[::-1] for line in (old/"SHA256SUMS").read_text().splitlines());assert digest(source)==manifest[source.name]
    frozen=subprocess.check_output(["git","show",BASE+":"+FILE],cwd=ROOT);assert (ROOT/FILE).read_bytes()==frozen
    selected={r["source_name"]:r for r in scan(frozen.decode(),FILE)};assert set(selected)==set(SPECS)==set(PINS) and len(SPECS)==11
    prior=set(BRIDGE_OUTCOME)|set(CLOSER_PAYABLE)|set(ASSIGNABLE)|set(PURE)|set(PATHS)|set(MIRRORS)|set(CLEAN_TAIL);assert len(prior)==104 and prior.isdisjoint(SPECS)
    historical=json.loads(source.read_text());assert historical["base"]==BASE
    originals={r["source_name"]:r for r in historical["declarations"]};assert len(originals)==500
    v.VERSION=json.loads((proof/"serial/baseline-results.json").read_text())["version"];v.FINGERPRINTS.clear();v.checked_module(proof/"serial",FILE)
    records=[]
    for name,spec in SPECS.items():
        row=originals[name];bs=row["elaborated"]["binders"]
        for key in ("source_name","file","line","kind","visibility","source_header","source_header_sha256","source_prefix_sha256","proving_owner","documented_producing_lane"):
            assert row[key]==selected[name][key],"Frozen source provenance changed"
        assert row["elaborated"]["name"]==PINS[name]["elaborated_name"] and row["elaborated"]["module"]==FILE[:-5].replace("/","."),"Frozen elaborated identity changed"
        assert hashlib.sha256(row["elaborated"]["type_expr"].encode()).hexdigest()==row["elaborated_type_sha256"]==PINS[name]["type_expr"]
        assert hashlib.sha256(json.dumps(bs,sort_keys=True,separators=(",",":")).encode()).hexdigest()==PINS[name]["binders"],"Frozen binder metadata changed"
        report={k:row[k] for k in ("source_name","file","line","visibility","source_header","documented_producing_lane","proving_owner")}
        report.update(theorem=name,historical_frozen_elaborated_name=PINS[name]["elaborated_name"],historical_frozen_elaborated_type_sha256=PINS[name]["type_expr"],binders=annotate_occurrences(name,bs,spec),interpretation=spec["notes"],designated_joint_certificate=v.certificate(proof/"serial",*v.WITNESSES[name]))
        records.append(report)
    out.mkdir(parents=True,exist_ok=True)
    payload=dict(frozen_assignment_base=BASE,current_head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),historical_typed_snapshot_sha256=digest(source),declarations=records,reviewed_reachable_mode_role_records=11,logical_premise_occurrences=sum(len(s["premises"]) for s in SPECS.values()),previous_disjoint_role_specifications=104,combined_disjoint_role_specifications=115,remaining_role_specifications=385,new_joint_interfaces=0,generated_candidates_dispositioned=0,full_assignment_acceptance=False,boundary="Eleven frozen mode telescopes and designated current packets checked; prior104 names checked for disjointness only. Separate reports total115, no merged115acceptance or whole-tree equivalence. No new compiler or physical EVM coverage.")
    (out/"reachable-mode-input-roles.json").write_text(json.dumps(payload,indent=2)+"\n")
    print("REACHABLE_MODE_INPUT_ROLES_PASS:11records;15logicaloccurrences;115disjointspecs;385rolesremaining;full_acceptance=false")
if __name__=="__main__":main()
