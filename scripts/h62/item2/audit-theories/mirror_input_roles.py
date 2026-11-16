#!/usr/bin/env python3
"""All13 memory-mirror premise roles, using exact frozen telescope pins.
Global heap relations remain distinct from selected-data mirror feasibility.
No new witness/interface coverage, strict-growth or target EVM claim is made.
"""
import argparse,hashlib,json,subprocess
from pathlib import Path
from census import ROOT,BASE,scan
from input_roles import annotate,digest,SPECS as BRIDGE_OUTCOME
from mutability_input_roles import SPECS as CLOSER_PAYABLE
from assignable_input_roles import SPECS as ASSIGNABLE
from pure_input_roles import SPECS as PURE
from path_input_roles import SPECS as PATHS
import verify_census as v
FILE="Solidity/Theory/Typed/MemMirror.lean"
NOTES=[
    'H and type/field shapes are intrinsic configuration data; hp and the numeric bounds are selected data. hn constrains these selected bounds and the anonymous premise relates THESE values in THIS heap. Both coexist with a populated heap and primitive or singleton aggregate mirrors; no arbitrary-heap or compiler-success law is assumed.',
    'The prefix e is a logical proof about the selected H/H-prime layouts, not an inhabited data instance. hk preserves EVERY old object reference for these SAME heaps and prefix; it is not preservation for all possible heap pairs. The mirror premise, n and all later value/container inputs coexist. Packets use a populated heap, singleton aggregates and reflexive prefix; they do not establish strict heap-growth case coverage or physical EVM execution.',
    'The map-free check is per selected type, not a universal feasibility claim for every type. A real nonempty storage array is copied into an already populated heap, or a singleton vector is copied; the copy result mirrors the selected input. No target memory, gas or compiler-success claim follows.',
    'h quantifies every member of THIS selected field list. The list is a singleton with a real bool field, so map-free is not discharged by an empty catalogue. The heap, source fields and whole quantified condition coexist; no assertion of all field lists or physical execution is made.',
    'The anonymous mirror premise constrains this selected storage value and memory value/reference in a populated heap. The object packet chooses an actual array reference; the impossible mapping branch does not make the generic theorem an H69 refutation. No extra premise is installed on the original statement.',
    'The named member type T and lookup-success hf occur AFTER the mirror premise and remain inputs. A singleton named bool field supplies the whole mirror and a successful lookup together, not independent inhabitance of each condition.',
    'The index i AFTER the mirror premise remains a full input. The frozen theorem has NO in-bounds hypothesis: it handles both jointly absent and successfully mirrored reads. The designated packet additionally selects i=0 in a singleton vector, with i<k only as fixture support; this does not add a bound premise to the public theorem.',
]
ROWS=[
    ('Solidity.SVal.Mirrors.mono', "H hp n n' hn T v w a._@._internal._hyg.0", 'H T', {'hn': 'per-input-selected-bound-order', 'a._@._internal._hyg.0': 'per-input-correlated-mirror'}, 0, '7a17fe36b5c8e7a419178ed087f970ae6850ebee7b86894e2b38b172af7278bb', '35f5873817dcdbf7bddb03b740edc7457a745366edfc75c7694383c759c0b579'),
    ('Solidity.SFields.Mirrors.mono', "H hp n n' hn fs x o a._@._internal._hyg.0", 'H fs', {'hn': 'per-input-selected-bound-order', 'a._@._internal._hyg.0': 'per-input-correlated-mirror'}, 0, '946541119be0914814538346e79eecb3925b113b766b5e2fe80deb9c5684215a', '8667276f094f6f462688fe39577032d71e0f348fc97cbbb3ac56347238f62d51'),
    ('Solidity.SVec.Mirrors.mono', "H hp n n' hn E k x l a._@._internal._hyg.0", 'H E', {'hn': 'per-input-selected-bound-order', 'a._@._internal._hyg.0': 'per-input-correlated-mirror'}, 0, 'e8d9158a3f692e9c1f8f1fdc4f14d120e29284b7aa499707af25af1e3ae71f81', '12dc3938e086f7024556f08be62d3acbcf10dfedff555101ff16fa430fdd26d5'),
    ('Solidity.SVal.Mirrors.wk', "H H' e hp hp' hk n T v w a._@._internal._hyg.0", "H H' T", {'e': 'selected-layout-prefix-proof', 'hk': 'all-old-references-preservation-for-fixed-heap-pair', 'a._@._internal._hyg.0': 'per-input-correlated-mirror'}, 1, '0a7f947f04b08ace6aab7bb2d54b47e6ae2e95f34f014d3855c73c4b8277e6a8', '7a402ce3d025b01778ae5468c938e3d7dbfa96f9cdef5305965e9c5e270fcf16'),
    ('Solidity.SFields.Mirrors.wk', "H H' e hp hp' hk n fs x o a._@._internal._hyg.0", "H H' fs", {'e': 'selected-layout-prefix-proof', 'hk': 'all-old-references-preservation-for-fixed-heap-pair', 'a._@._internal._hyg.0': 'per-input-correlated-mirror'}, 1, '729db69dd328765acd9029b9b1ed3706a4072138b781b6db3878cdf6beb83759', 'bdfac3dafdd299794c88789395a0477a18be59161c7eefa38b52dfd976233e05'),
    ('Solidity.SVec.Mirrors.wk', "H H' e hp hp' hk n E k x l a._@._internal._hyg.0", "H H' E", {'e': 'selected-layout-prefix-proof', 'hk': 'all-old-references-preservation-for-fixed-heap-pair', 'a._@._internal._hyg.0': 'per-input-correlated-mirror'}, 1, 'f8a539459afdb5bd310e4ba21d897865dfa1e4cefcb1289b21b6e36d8cae16b4', '2d2c527b299d682de8e0bc6041b13c98acd81e88fb175842423329201da41a14'),
    ('Solidity.SVal.mirrors_copyStToM', 'H hp T v h', 'H T', {'h': 'per-selected-type-map-free-check'}, 2, 'a9c14d7634ac05a7fbfac53e6953eda0d9f8b90f6817f910c80d6615ca699228', '215f5112a66eedc6b97e065585558ccd8be8600219a2a9cd2ad398fa900c26f4'),
    ('Solidity.SFields.mirrors_copyStToM', 'H hp fs x h', 'H fs', {'h': 'all-members-map-free-for-selected-field-list'}, 3, '264c7610eb921bfb84a98ba46d393fbf196c1c7dc25f28eb77d13e213b3fb3c5', '1d8997108bf575d288fdb404b66fd43ec2c5c4ae7852ca16f6bfffce4586768a'),
    ('Solidity.SVec.mirrors_copyStToM', 'H hp E k x h', 'H E', {'h': 'per-selected-type-map-free-check'}, 2, '5b9e77508a41b26f2e50b2596c846bd55c00bc7700057559eb191b8c5869ff49', '896e14d3910d003e4aa43855f9c83a312056af0786fa1385b05e3a19ac8c48c3'),
    ('Solidity.SVal.Mirrors.prim', 'H hp n p v w a._@._internal._hyg.0', 'H p', {'a._@._internal._hyg.0': 'per-input-correlated-mirror'}, 4, '13adfc46bb1483f448a0d7fe172a4d10e8f5e6c85e390a978663e1bd114553a4', 'a4e242028e156a185aa048cd36eb584b6f82b62e16a31aacb13b2070f3b73d40'),
    ('Solidity.SVal.Mirrors.id_ge', 'H hp n R v r a._@._internal._hyg.0', 'H R', {'a._@._internal._hyg.0': 'per-input-correlated-mirror'}, 4, 'ae2f0a7b304043dd920d34ab83d2d1ea344b3da03a227cb9f74646e12bc02e9d', '30268f82750526d27960b3967b80210f691cb4cd06f76321ed8ccc3eaf05e5ea'),
    ('Solidity.SFields.Mirrors.get', 'H hp n f fs x o a._@._internal._hyg.0 T hf', 'H fs T', {'a._@._internal._hyg.0': 'per-input-correlated-fields-mirror', 'hf': 'per-input-selected-member-lookup-success'}, 5, '12bbb867328bd980c0bcb1a22b1bced4aa8a919a58fc8dd5c09442d9c1a3ec39', '1ed2e0fcc0d8e419688c540eaedcea17fca63d2df663b802baabf6d31c191aee'),
    ('Solidity.SVec.Mirrors.getElem', 'H hp n E k x l a._@._internal._hyg.0 i', 'H E', {'a._@._internal._hyg.0': 'per-input-correlated-vector-mirror'}, 6, 'afffebf63e827ed94a91f620235a96898df62f91a68065c01715e1f11c140794', 'c6a1de91f90c1661d9c7fe33d29a7cf8b7d3fbb2fbc5f2d2a23acaec4146d0ab'),
]
SPECS={name:dict(binders=bs.split(),configuration=cfg.split(),premises=props,notes=NOTES[note]) for name,bs,cfg,props,note,_,_ in ROWS}
PINS={name:dict(type_expr=ty,binders=bs) for name,_,_,_,_,ty,bs in ROWS}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ("proof-evidence","historical-evidence","out"):ap.add_argument("--"+name,type=Path,required=True)
    a=ap.parse_args();proof=a.proof_evidence.resolve();old=a.historical_evidence.resolve();out=a.out.resolve()
    if any(p.is_relative_to(ROOT) for p in (proof,old,out)):raise SystemExit("Use off-Git evidence")
    source=old/"verified-census.json";manifest=dict(line.split("  ",1)[::-1] for line in (old/"SHA256SUMS").read_text().splitlines())
    assert digest(source)==manifest[source.name],"Historical snapshot hash mismatch"
    frozen=subprocess.check_output(["git","show",BASE+":"+FILE],cwd=ROOT)
    assert (ROOT/FILE).read_bytes()==frozen,"Selected frozen interface changed"
    selected={r["source_name"]:r for r in scan(frozen.decode(),FILE)}
    assert set(selected)==set(SPECS)==set(PINS) and len(SPECS)==13
    prior=set(BRIDGE_OUTCOME)|set(CLOSER_PAYABLE)|set(ASSIGNABLE)|set(PURE)|set(PATHS)
    assert len(prior)==85 and prior.isdisjoint(SPECS)
    typed=json.loads(source.read_text());assert typed["base"]==BASE
    originals={r["source_name"]:r for r in typed["declarations"]};assert len(originals)==500
    v.VERSION=json.loads((proof/"serial/baseline-results.json").read_text())["version"];v.FINGERPRINTS.clear();v.checked_module(proof/"serial",FILE)
    records=[]
    for name,spec in SPECS.items():
        row=originals[name];bs=row["elaborated"]["binders"]
        for key in ("source_name","file","line","kind","visibility","source_header","source_header_sha256","source_prefix_sha256","proving_owner","documented_producing_lane"):
            assert row[key]==selected[name][key],"Frozen source provenance changed"
        assert row["elaborated"]["name"]==name and row["elaborated"]["module"]==FILE[:-5].replace("/","."),"Frozen elaborated identity changed"
        assert hashlib.sha256(row["elaborated"]["type_expr"].encode()).hexdigest()==row["elaborated_type_sha256"]==PINS[name]["type_expr"]
        assert hashlib.sha256(json.dumps(bs,sort_keys=True,separators=(",",":")).encode()).hexdigest()==PINS[name]["binders"],"Frozen binder metadata changed"
        report=annotate(row,spec)
        for b in report["binders"]:
            if b["name"].startswith("inst."):b["role"]="global-location-algebra-instance-data-with-laws"
        assert name in v.WITNESSES and name not in v.IMPOSSIBLE
        report["designated_joint_certificate"]=v.certificate(proof/"serial",*v.WITNESSES[name]);records.append(report)
    out.mkdir(parents=True,exist_ok=True)
    payload=dict(frozen_assignment_base=BASE,current_head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),historical_typed_snapshot_sha256=digest(source),declarations=records,reviewed_mirror_role_records=13,previous_disjoint_role_specifications=85,combined_disjoint_role_specifications=98,remaining_role_specifications=402,new_joint_interfaces=0,generated_candidates_dispositioned=0,full_assignment_acceptance=False,boundary="13 frozen mirror telescopes and current joint packets checked. Prior85 role names checked for disjointness only here; separate legacy44 and Path41 reports retain their own validation scope. No whole-tree dependent-definition equivalence, strict heap-growth coverage or physical EVM guarantee.")
    (out/"mirror-input-roles.json").write_text(json.dumps(payload,indent=2)+"\n")
    print("MIRROR_INPUT_ROLES_PASS:13checked;98disjointspecifications;402rolesremaining;0newinterfaces;full_acceptance=false")
if __name__=="__main__":main()
