#!/usr/bin/env python3
"""Exact two-stage coverage packet accounting; not kernel or full-family acceptance."""
import argparse, hashlib, json, re, subprocess
from pathlib import Path
import census
BASE="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
MODULE="Solidity/Backend/StorageOps/TargetNestedArrayTransportControls.lean"
PATTERN='  · intro k inside j (?P<v>\\w+)\\n    change k < 2 at inside\\n    have casesK : k = 0 ∨ k = 1 := by omega\\n    rcases casesK with rfl \\| rfl\\n    · change j < 3 at (?P=v)\\n      have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega\\n      rcases casesJ with rfl \\| rfl \\| rfl <;> decide\\n    · change j < 2 at (?P=v)\\n      have casesJ : j = 0 ∨ j = 1 := by omega\\n      rcases casesJ with rfl \\| rfl <;> decide\\n'
PATTERN_ONE='  · intro k inside j live\\n    change k < 2 at inside\\n    have casesK : k = 0 ∨ k = 1 := by omega\\n    rcases casesK with rfl \\| rfl <;> change j < 1 at live\\n    all_goals have same : j = 0 := by omega\\n    all_goals subst j; decide\\n'
MARKER='open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph\n'
HELPER="\n/-- Convert bounded natural-index coverage to the identical dependent finite\nindex family. Bounds remain arbitrary; this imposes no source-program cap. -/\ntheorem forall_bounded_pair {outer : Nat} {inner : Nat → Nat} {P : Nat → Nat → Prop}\n    (finite : ∀ i : Fin outer, ∀ j : Fin (inner i.val), P i.val j.val) :\n    ∀ i, i < outer → ∀ j, j < inner i → P i j :=\n  fun i hi j hj => finite ⟨i, hi⟩ ⟨j, hj⟩\n\n/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.forall_bounded_pair' does not depend on any axioms -/\n#guard_msgs (whitespace := lax) in #print axioms forall_bounded_pair\n"
REPLACEMENT="  · exact forall_bounded_pair (by decide)\n"
def digest(raw):return hashlib.sha256(raw).hexdigest()
def expected(original):
    if not isinstance(original,bytes):raise ValueError("raw original bytes required")
    text=original.decode("utf-8")
    if text.count(MARKER)!=1 or "theorem forall_bounded_pair" in text:raise ValueError("unexpected original header")
    text,count=re.subn(PATTERN,REPLACEMENT,text)
    if count!=15:raise ValueError("original first proof-case count changed")
    text,second=re.subn(PATTERN_ONE,REPLACEMENT,text)
    if second!=15:raise ValueError("original second proof-case count changed")
    return text.replace(MARKER,MARKER+HELPER,1).encode("utf-8")
def verify(original,current):
    if not isinstance(current,bytes) or current!=expected(original):raise ValueError("packet source drift")
    old=census.declarations(original.decode("utf-8"),MODULE);new=census.declarations(current.decode("utf-8"),MODULE)
    a={d["name"]:d for d in old};b={d["name"]:d for d in new}
    added="Solidity.Backend.StorageOps.TargetNestedArrayTransportControls.forall_bounded_pair"
    if len(a)!=len(old) or len(b)!=len(new) or set(b)-set(a)!={added} or not set(a)<=set(b):raise ValueError("declaration loss/duplication")
    for name,row in a.items():
        if row["statement_sha256"]!=b[name]["statement_sha256"]:raise ValueError("original statement drift")
        if row["kind"] not in ("theorem","lemma") and row["declaration_sha256"]!=b[name]["declaration_sha256"]:raise ValueError("fixture definition drift")
    changed=[n for n in a if a[n]["declaration_sha256"]!=b[n]["declaration_sha256"]]
    if len(changed)!=15:raise ValueError("unexpected proof-body count")
    return {"base":BASE,"module":MODULE,"original_declarations":len(a),"added_theorem":added,
            "changed_proof_names":sorted(changed),"coverage_subproofs_replaced":30,"original_sha256":digest(original),"candidate_sha256":digest(current),
            "all_original_statements_and_definitions_preserved":True,
            "boundary":"Exact source/signature/fixture accounting only; kernel, axioms, timings and full-family acceptance are separate."}
def main():
    ap=argparse.ArgumentParser();ap.add_argument("--output",type=Path,required=True);args=ap.parse_args()
    root=Path(subprocess.check_output(["git","rev-parse","--show-toplevel"],text=True).strip())
    if args.output.resolve().is_relative_to(root):ap.error("bulk output must be outside checkout")
    original=subprocess.check_output(["git","show",BASE+":"+MODULE],cwd=root)
    report=verify(original,(root/MODULE).read_bytes());args.output.write_text(json.dumps(report,indent=2)+"\n")
    print("FINITE_COVERAGE_PACKET_PRESERVATION_PASS")
if __name__=="__main__":main()
