#!/usr/bin/env python3
"""All six frozen leaf-extension telescopes, with all-horizon premise laws.
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
from indexed_roles import annotate_occurrences
import verify_census as v
FILE="Solidity/Theory/Progress/Leaves.lean"
NOTES=['All E/G/A/Q inputs are configuration DATA. A and Q are predicate-valued functions, not proofs of allowed calls or frame '
 'eligibility. Soundness is the CONCLUSION, not an extra input premise. The shared packet also supplies one actual Q frame and '
 'an admitted successful builtin node; no event-emission operational result is inferred.',
 'All E/G/A/Q inputs coexist. No logical premise occurs in this telescope; the extension soundness conclusion is not assumed. '
 'The shared builtin success supports a real source configuration, not execution of a custom-error node. Custom-error '
 'operational coverage remains outstanding.',
 'hAll is the WHOLE law over EVERY horizon n and EVERY frame F under Q F.contract, for the SAME E/G/A/Q. It is not just the '
 'selected successful horizon or one frame. A=False is disclosed as call-free, while Q=True has an actual frame so '
 'frame-predicate emptiness does not supply the proof. An actually admitted require(true) node succeeds independently for every '
 'compatible state under both source pipelines.',
 'The same whole all-horizon/all-frame expression law is preserved; hAll is logical, while A/Q are DATA. The global law and real '
 'Q frame, admitted builtin node and success coexist. No internal function admission, event/custom-error operation or target '
 'compiler success follows from the call-free fixture.',
 'No input soundness law occurs: E/G/A/Q are configuration data. Combining emit and custom-error soundness is the conclusion. '
 'The packet supplies an actual configuration and real successful builtin support, without claiming that builtin support is an '
 'emit/custom-error execution.',
 'Call-free fixes A=False IN THE ORIGINAL STATEMENT; E/G/Q remain the only declared data inputs. Q=True has a real frame, and '
 'builtin admission/success is independently checked. No extra hAll hypothesis is invented, and no admitted internal declaration '
 'or compiler/EVM/gas/fork coverage is claimed.']
ROWS=[('Solidity.Theory.Progress.emitExt_sound',
  'E G A Q',
  [0, 1, 2, 3],
  {},
  0,
  'b751a35940eba2c6bc2e3e4e881fdcc4ff103051109459599ae58fe6f72f187e',
  '7f0ce5e73dfe31550a20dd0ecc914453f53615783651884ea8430f158addb1ae',
  'Solidity.Theory.Progress.emitExt_sound'),
 ('Solidity.Theory.Progress.revertErrorExt_sound',
  'E G A Q',
  [0, 1, 2, 3],
  {},
  1,
  'c9c5ecadcc9abe5035483fcfc634d71a491d8ef6183db33a3cc073cb35d0a909',
  '7f0ce5e73dfe31550a20dd0ecc914453f53615783651884ea8430f158addb1ae',
  'Solidity.Theory.Progress.revertErrorExt_sound'),
 ('Solidity.Theory.Progress.builtinExt_sound',
  'E G A Q hAll',
  [0, 1, 2, 3],
  {4: 'all-horizons-and-all-Q-frames-expression-progress-for-fixed-configuration'},
  2,
  '0cc5c3d43eedaa3c8b34720e21ef547582d04ec3a92ead57be05126902a4aedb',
  'd2bf9961d7a987ca9aefbe4b865b071000bfb2e85f03433224ffa5376ce7d8c0',
  'Solidity.Theory.Progress.builtinExt_sound'),
 ('Solidity.Theory.Progress.leafExt_sound',
  'E G A Q hAll',
  [0, 1, 2, 3],
  {4: 'all-horizons-and-all-Q-frames-expression-progress-for-fixed-configuration'},
  3,
  '67f32979587afdb3d85798e2a37db44c96bfa3348683b2a2199a6be01f88ec8a',
  'd2bf9961d7a987ca9aefbe4b865b071000bfb2e85f03433224ffa5376ce7d8c0',
  'Solidity.Theory.Progress.leafExt_sound'),
 ('Solidity.Theory.Progress.effectExt_sound',
  'E G A Q',
  [0, 1, 2, 3],
  {},
  4,
  '8ffbd41a123354b99c05e6ee16fa39bc0db5f8912313d6362256207e7108eb9d',
  '7f0ce5e73dfe31550a20dd0ecc914453f53615783651884ea8430f158addb1ae',
  'Solidity.Theory.Progress.effectExt_sound'),
 ('Solidity.Theory.Progress.leafExt_sound_callFree',
  'E G Q',
  [0, 1, 2],
  {},
  5,
  '4608b83054443840aaf90b5cea18bd3e8a8d6dbf6833eb612e816e4f1d429663',
  '8bbcf6bf88f59f0c33f2fbd9f9152696909b7be722acd46504ea647745de708a',
  'Solidity.Theory.Progress.leafExt_sound_callFree')]
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
    prior=set(BRIDGE_OUTCOME)|set(CLOSER_PAYABLE)|set(ASSIGNABLE)|set(PURE)|set(PATHS)|set(MIRRORS)|set(CLEAN_TAIL)|set(MODES);assert len(prior)==115 and prior.isdisjoint(SPECS)
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
        report.update(theorem=name,historical_frozen_elaborated_name=PINS[name]["elaborated_name"],historical_frozen_elaborated_type_sha256=PINS[name]["type_expr"],binders=annotate_occurrences(name,bs,spec),interpretation=spec["notes"],designated_joint_certificate=v.certificate(proof/"serial",*v.WITNESSES[name]))
        records.append(report)
    out.mkdir(parents=True,exist_ok=True)
    payload=dict(frozen_assignment_base=BASE,current_head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),historical_typed_snapshot_sha256=digest(source),declarations=records,reviewed_leaf_progress_role_records=6,logical_premise_occurrences=sum(len(s["premises"]) for s in SPECS.values()),previous_disjoint_role_specifications=115,combined_disjoint_role_specifications=121,remaining_role_specifications=379,new_joint_interfaces=0,generated_candidates_dispositioned=0,full_assignment_acceptance=False,boundary="Six frozen leaf telescopes and designated original-history packets checked; prior115 names checked for disjointness only. Separate reports total121, no merged121acceptance or whole-tree equivalence. Builtin source support does not claim event/error operations or compiler/physical coverage.")
    (out/"leaf-progress-input-roles.json").write_text(json.dumps(payload,indent=2)+"\n")
    print("LEAF_PROGRESS_INPUT_ROLES_PASS:6records;2logicaloccurrences;121disjointspecs;379rolesremaining;full_acceptance=false")
if __name__=="__main__":main()
