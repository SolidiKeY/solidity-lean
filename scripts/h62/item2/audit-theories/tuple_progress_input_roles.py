#!/usr/bin/env python3
"""All six frozen tuple telescopes, with repeated-name and H69 distinctions.
Original theorem identity and typed/source/owner provenance remain frozen.
Run in the original historical checkout; current-tree coverage is separate.
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
from reachable_mode_input_roles import SPECS as MODES
from leaf_progress_input_roles import SPECS as LEAVES
from indexed_roles import annotate_occurrences
import verify_census as v
FILE="Solidity/Theory/Progress/Tuple.lean"
NOTES=['Intentional H69 type-separation refutation: no plain Val can have a tuple type, for ANY layout or component types. D/types/v '
 'are data binders but their joint input is impossible; the checked no_plain_tuple_input proof is the audit result, not a joint '
 'witness or operational refusal. Do not confuse this Val with the inhabited RVal.tuple in the next theorem.',
 'D/types/v are correlated data, with no logical premise. The SAME nonempty three-boolean RVal.tuple has actual components and '
 'successful untupling. This is the inhabited runtime tuple domain, distinct from the intentional plain-Val impossibility.',
 'E/output-frame Gamma-prime/F/n and selected slots/types/runtime values/Gamma/locals coexist. The two logical hypotheses have '
 'the SAME anonymous printed name but DIFFERENT types and positions: exact slotsFit=true and SlotsOK. Neither replaces the '
 'other. Both hold with two declared bool slots, a discarded middle component and an actual successful push. The public '
 'declaration constructor infers exactly the frozen fit proof; its current mapFree variant is separately checked, not asserted '
 'equivalent.',
 'The FIRST anonymous logical occurrence is the WHOLE ExprNSAt law for EVERY lower horizon m<=n at the SAME A/G/F; the SECOND is '
 'selected ArgsFragment membership. Their identical names do not merge them. Later types/es are retained AFTER the global law. '
 'Call-free A=False is explicit, while nonempty arguments actually return at horizon8; no internal function admission or target '
 'compiler success is inferred.',
 'hE is the whole lower-horizon expression law for the SAME fixed configuration, not only one successful expression evaluation. '
 'Gamma/types/e occur AFTER hE; hi is per-selected-initializer TupleInit. All data, the whole law and the literal initializer '
 'predicate coexist with successful nonempty tuple evaluation.',
 'All inherited E/A/G/F/n/nps/ph/R/M/k/Gamma/types/slots/e inputs and FOUR proofs coexist: whole lower-horizon hE, exact '
 'slotsFit=true, selected TupleInit and selected SlotsOK. Locals l occur AFTER the fit proof and remain correlated. The public '
 'constructor pins fit to exact slots/types/environment. Positive n+1=10 declaration execution is actual source support, with no '
 'EVM gas/fork/compiler inference.']
ROWS=[('Solidity.Theory.Progress.Val.not_tuple',
  'D σs v',
  [0, 1],
  {},
  0,
  '2a9280bf3faf890475426582e34f8b2daeeb195a34d0b3486b05675874c57977',
  '217d737ceca23282772bb2197f82fa4b933835d015157b8a8bd7afa0219b91b3',
  'Solidity.Theory.Progress.Val.not_tuple'),
 ('Solidity.Theory.Progress.RVal.untuple_ok',
  'D σs v',
  [0, 1],
  {},
  1,
  '14745575bd686089317584d1db7cdfddda80d949207432a6752cf09d80f615c2',
  '899e010a35a1cab4b3f953fe0402348480bdf5ff7b97b2c99577a803545f4ff6',
  'Solidity.Theory.Progress.RVal.untuple_ok'),
 ('Solidity.Theory.Progress.pushVals_ns',
  "E Γ' F n slots σs vs Γ l a._@._internal._hyg.0 a._@._internal._hyg.0",
  [0, 1, 2, 3],
  {9: 'per-input-exact-slotsFit-true', 10: 'per-input-selected-SlotsOK'},
  2,
  '84da4f5e3133f2c94d674b8be0ba824ae6236f92cfeb704828cf0f2ac6ff0b8e',
  'dabcc2f05652c3f3bba97f3b14f19e6f713464043c3dd07a71d4eef9e03f79c4',
  'Solidity.Theory.Progress.pushVals_ns'),
 ('Solidity.Theory.Progress.argsFragment_le',
  'E A G F Γ n a._@._internal._hyg.0 ts es a._@._internal._hyg.0',
  [0, 1, 2, 3],
  {6: 'all-lower-horizons-expression-progress-for-fixed-configuration', 9: 'per-input-selected-ArgsFragment'},
  3,
  '68586b5d865b9a1091ed83f127cf1d2488aa2c1575fac69aeb84595c6057a29c',
  '1b4089fe03075e7b12afd1b2cf90440845d3f1392539ca48dd9dd08b7294a20f',
  'Solidity.Theory.Progress.argsFragment_le'),
 ('Solidity.Theory.Progress.tupleInit_ns',
  'E A G F n hE Γ σs e hi',
  [0, 1, 2, 3],
  {5: 'all-lower-horizons-expression-progress-for-fixed-configuration', 9: 'per-input-selected-TupleInit'},
  4,
  '21c475c781fa29e312a232beee09f7c92ca179c4112fb583003c3c58361a440b',
  'e662f3e42988e9111dbb322a03448a65c24500bb3eac16f00913b4247ad19b16',
  'Solidity.Theory.Progress.tupleInit_ns'),
 ('Solidity.Theory.Progress.declTuple_ns',
  'E A G F n hE nps ph R M k Γ σs slots e h l hi hs',
  [0, 1, 2, 3],
  {5: 'all-lower-horizons-expression-progress-for-fixed-configuration',
   15: 'per-input-exact-slotsFit-true',
   17: 'per-input-selected-TupleInit',
   18: 'per-input-selected-SlotsOK'},
  5,
  '08a0352a4e12384f433f84b8ea179828a4fc329c750dc6280fbf63f33443a95f',
  '6a10b096f3ee651d2b0cd23f3671d188c984172adc2a65e8fe24ff3525dca175',
  'Solidity.Theory.Progress.declTuple_ns')]
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
    prior=set(BRIDGE_OUTCOME)|set(CLOSER_PAYABLE)|set(ASSIGNABLE)|set(PURE)|set(PATHS)|set(MIRRORS)|set(CLEAN_TAIL)|set(MODES)|set(LEAVES);assert len(prior)==121 and prior.isdisjoint(SPECS)
    assert set(SPECS)&set(v.IMPOSSIBLE)=={"Solidity.Theory.Progress.Val.not_tuple"}
    historical=json.loads(source.read_text());assert historical["base"]==BASE
    originals={r["source_name"]:r for r in historical["declarations"]};assert len(originals)==500
    v.VERSION=json.loads((proof/"serial/baseline-results.json").read_text())["version"];v.FINGERPRINTS.clear();v.checked_module(proof/"serial",FILE)
    records=[]
    for name,spec in SPECS.items():
        row=originals[name];bs=row["elaborated"]["binders"]
        for key in ("source_name","file","line","kind","visibility","source_header","source_header_sha256","source_prefix_sha256","proving_owner","documented_producing_lane"):
            assert row[key]==selected[name][key],"Frozen source provenance changed"
        assert row["elaborated"]["name"]==PINS[name]["elaborated_name"] and row["elaborated"]["module"]==FILE[:-5].replace("/","."),"Frozen elaborated identity changed"
        assert hashlib.sha256(row["elaborated"]["type_expr"].encode()).hexdigest()==row["elaborated_type_sha256"]==PINS[name]["type_expr"],"Frozen elaborated type changed"
        assert hashlib.sha256(json.dumps(bs,sort_keys=True,separators=(",",":")).encode()).hexdigest()==PINS[name]["binders"],"Frozen binder metadata changed"
        report={k:row[k] for k in ("source_name","file","line","visibility","source_header","documented_producing_lane","proving_owner")}
        report.update(theorem=name,historical_frozen_elaborated_name=PINS[name]["elaborated_name"],historical_frozen_elaborated_type_sha256=PINS[name]["type_expr"],binders=annotate_occurrences(name,bs,spec),interpretation=spec["notes"])
        if name in v.IMPOSSIBLE:
            report.update(input_disposition="intentional-H69-impossibility",intentional_reason=spec["notes"],designated_impossibility_certificate=v.certificate(proof/"serial",*v.IMPOSSIBLE[name]))
        else:
            report.update(input_disposition="ordinary-joint-witness",designated_joint_certificate=v.certificate(proof/"serial",*v.WITNESSES[name]))
        records.append(report)
    out.mkdir(parents=True,exist_ok=True)
    payload=dict(frozen_assignment_base=BASE,current_head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),historical_typed_snapshot_sha256=digest(source),declarations=records,reviewed_tuple_progress_role_records=6,ordinary_joint_records=5,intentional_H69_records=1,logical_premise_occurrences=sum(len(s["premises"]) for s in SPECS.values()),previous_disjoint_role_specifications=121,combined_disjoint_role_specifications=127,remaining_role_specifications=373,new_joint_interfaces=0,generated_candidates_dispositioned=0,full_assignment_acceptance=False,boundary="Six frozen tuple telescopes checked:five joint inputs and one intentional H69 impossibility. Prior121 names checked for disjointness only. Separate reports total127,no merged127acceptance or whole-tree equivalence. No new compiler/physical coverage.")
    (out/"tuple-progress-input-roles.json").write_text(json.dumps(payload,indent=2)+"\n")
    print("TUPLE_PROGRESS_INPUT_ROLES_PASS:6records;10logicaloccurrences;5joint+1H69;127disjointspecs;373rolesremaining;full_acceptance=false")
if __name__=="__main__":main()
