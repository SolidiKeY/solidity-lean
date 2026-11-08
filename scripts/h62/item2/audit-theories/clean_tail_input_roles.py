#!/usr/bin/env python3
"""All6 clean-tail telescopes; anonymous hypotheses are classified by occurrence.
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
from indexed_roles import annotate_occurrences
import verify_census as v
FILE="Solidity/Theory/Reachable/CleanTail.lean"
NOTES=[
    'P is hereditary-predicate DATA, not a global assumption that every value satisfies it. The same P/fs/L coexist with distinct source x and replacement y. The two logical All premises have the SAME printed anonymous name but DIFFERENT occurrences and types; both are retained separately. The packet copies true over false in a nonempty field list.',
    'C carries intrinsic contract data; st is one actual selected clean storage. Its global contract contains a transient flag and a persistent one-element array. The true transient flag resets to false; a separate checked observation preserves the successful live-array read. This is source-model reset behavior, not physical TSTORE/gas semantics.',
    'The original declaration stays PRIVATE; its exact frozen elaborated name is pinned. C/Gamma/state are correlated data and h constrains this selected storage. The packet supplies real transient reset observations and clean storage in the SAME state. No visibility or statement is changed.',
    'ExposesNone quantifies EVERY constructor argument and EVERY action of this fixed M. It is not a per-selected-call check or an assertion that every possible interface is feasible. Unit/Unit domains are inhabited, and the SAME interface has a successful constructor, admitted entry and observable flag write; empty argument domains and reject-all runs are not used.',
    'The global ExposesNone law and the later selected state sigma/EntryState proof coexist. EntryState supplies one actual reachable deployment world, accepted transaction, zero-value admission, allowCall proof and successful entry, not all states or merely default-storage inhabitance. The shared fixture also has a genuine successful body.',
    'h is universal validity over ALL compatible typed states UNDER the clean-tail formula premise for this FIXED phi; it is not all formulas, every program or unconditional state validity. The same M satisfies the whole ExposesNone law and has an actual reachable entry state. No reachable-domain emptiness or change of default mode is used.',
]
ROWS=[
    ('Solidity.SFields.all_anon', 'P fs L x y a._@._internal._hyg.0 a._@._internal._hyg.0', [0, 1], {5: 'per-input-source-fields-All', 6: 'per-input-replacement-fields-All'}, 0, 'e51392b0aecec149def879b4bcef50ead513d6e94bd11e4f196159e7641b8a91', '91cd013bccbb4adab6b4f78b8284e4e0067699d3f6efa19251667333aadf1c4c', 'Solidity.SFields.all_anon'),
    ('Solidity.Storage.resetTransient_cleanTail', 'C st h', [0], {2: 'per-input-selected-storage-clean-tail'}, 1, '6fa1c30050c841c2522a486b7fb3f81b3040684e4487f5409367afd9d86e60d6', '63a6044737b4e85e9b59f58154cb734011f09e66031f423529e9fdb9c6f874fc', 'Solidity.Storage.resetTransient_cleanTail'),
    ('Solidity.Reachable.ofState_clean', 'C Γ σ h', [0, 1], {3: 'per-input-selected-state-storage-clean-tail'}, 2, '1917df772f223f19090c0830a5137e4f71806fe1c38b97ce13c96ad848250a68', 'bfa94aa1dfb319940cd03e932d2f480de707a53e8070e5cc2f85446f407bbb71', '_private.Solidity.Theory.Reachable.CleanTail.0.Solidity.Reachable.ofState_clean'),
    ('Solidity.Reachable.cleanTail_invariant', 'C D A M hM', [0, 1, 2], {4: 'all-constructors-and-actions-no-exposure-for-fixed-interface'}, 3, 'da81a2999f27785e18ad96aeb91e8d9ff40635d5c9a0eefa7c1d89fb2543abef', '85317dc2a59b4f7572201096c0548103ef0d200543d8a86c2ea594d1748fb6d4', 'Solidity.Reachable.cleanTail_invariant'),
    ('Solidity.Reachable.EntryState.cleanTail', 'C D A M hM σ h', [0, 1, 2], {4: 'all-constructors-and-actions-no-exposure-for-fixed-interface', 6: 'per-input-selected-reachable-admitted-entry'}, 4, '745150e02014f71c7ea27038aaa9a471b7394d1f09a28148b681c14f42767053', '18463b360bc1519dc1af4872566d78416224a78e437187d6c6e91befe7c39d44', 'Solidity.Reachable.EntryState.cleanTail'),
    ('Solidity.ValidTail.validStart_reachable', 'C D A M hM φ h', [0, 1, 2], {4: 'all-constructors-and-actions-no-exposure-for-fixed-interface', 6: 'all-compatible-states-conditional-validity-for-fixed-formula'}, 5, '6b37ccbb2888c5f3b7cab5ae6f6bcdbf567879b3cda57433ed04f043bce2ae41', '50d55e2182f3802b03b765cde332288bcd99c3a25c4b67a23c6d859071fe61ea', 'Solidity.ValidTail.validStart_reachable'),
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
    selected={r["source_name"]:r for r in scan(frozen.decode(),FILE)};assert set(selected)==set(SPECS)==set(PINS) and len(SPECS)==6
    prior=set(BRIDGE_OUTCOME)|set(CLOSER_PAYABLE)|set(ASSIGNABLE)|set(PURE)|set(PATHS)|set(MIRRORS);assert len(prior)==98 and prior.isdisjoint(SPECS)
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
    payload=dict(frozen_assignment_base=BASE,current_head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),historical_typed_snapshot_sha256=digest(source),declarations=records,reviewed_clean_tail_role_records=6,logical_premise_occurrences=sum(len(s["premises"]) for s in SPECS.values()),previous_disjoint_role_specifications=98,combined_disjoint_role_specifications=104,remaining_role_specifications=396,new_joint_interfaces=0,generated_candidates_dispositioned=0,full_assignment_acceptance=False,boundary="Six frozen telescopes and designated current joint packets checked. Prior98 names checked for disjointness only here; independent legacy44/Path41/Mirror13 reports remain separate. Private source identity preserved; repeated names do not collapse distinct binder occurrences. No whole-tree equivalence or physical compiler coverage.")
    (out/"clean-tail-input-roles.json").write_text(json.dumps(payload,indent=2)+"\n")
    print("CLEAN_TAIL_INPUT_ROLES_PASS:6records;9logicaloccurrences;104disjointspecs;396rolesremaining;full_acceptance=false")
if __name__=="__main__":main()
