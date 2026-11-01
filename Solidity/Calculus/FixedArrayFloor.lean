import Solidity.Calculus.ArrayCut
import Solidity.Calculus.MemFloor

/-!
# Same-length flooring of fixed storage vectors

Reuse the integrated memory lane's index-floor laws on intrinsic storage
vectors. Including the length breakpoint preserves optional reads even
outside the array. This additive semantic interface does not extend the
array-block classifier or claim a new decision verdict.
-/
namespace Solidity.Decide

/-- Rebuild exactly `n` typed storage elements at their natural-index floors. -/
def fixedFloorVec {E : Ty} {n : Nat} (B : List Int) (v : SVec E n) : SVec E n :=
  vecOf (fun k => v.toList.getD (mxFloorIndex B k) (SVal.dflt E)) n

/-- The reconstruction keeps the intrinsic fixed length. -/
theorem fixedFloorVec_length {E : Ty} {n : Nat} (B : List Int) (v : SVec E n) :
    (fixedFloorVec B v).toList.length = n := SVec.length_toList _

/-- Optional reads agree at every natural index, including halted reads. -/
theorem fixedFloorVec_slot {E : Ty} {n : Nat} (B : List Int) (v : SVec E n)
    (hn : (n : Int) ∈ B) (k : Nat) :
    (fixedFloorVec B v).toList[k]? = v.toList[mxFloorIndex B k]? := by
  rw [fixedFloorVec, vecOf_toList, List.getElem?_map]
  by_cases hk : k < n
  · have hf : mxFloorIndex B k < v.toList.length := by
      rw [SVec.length_toList]
      exact (mxFloorIndex_bounds B hn).2 hk
    rw [List.getElem?_range hk, Option.map_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hf]
    rfl
  · have hf : v.toList.length ≤ mxFloorIndex B k := by
      rw [SVec.length_toList]
      have hb : mxFloorIndex B k < n ↔ k < n := mxFloorIndex_bounds B hn
      omega
    rw [List.getElem?_eq_none (by rw [List.length_range]; omega), Option.map_none,
      List.getElem?_eq_none hf]

/-- Retained observations, whether present or halted, remain unchanged. -/
theorem fixedFloorVec_at {E : Ty} {n : Nat} (B : List Int) (v : SVec E n)
    (hn : (n : Int) ∈ B) {k : Nat} (hk : (k : Int) ∈ B) :
    (fixedFloorVec B v).toList[k]? = v.toList[k]? := by
  rw [fixedFloorVec_slot B v hn, mxFloorIndex_fix B hk]

/-- The natural floor remains a representable uint index. -/
def fixedFloorIndex (B : List Int) (i : PrimTy.uint.Denote) : PrimTy.uint.Denote :=
  uintOfNat (mxFloorIndex B i.1.toNat)

theorem fixedFloorIndex_toNat (B : List Int) (i : PrimTy.uint.Denote) :
    (fixedFloorIndex B i).1.toNat = mxFloorIndex B i.1.toNat := by
  have hle : mxFloorIndex B i.1.toNat ≤ i.1.toNat := mxFloorIndex_le B i.1.toNat
  have hlt : i.1.toNat < 2 ^ 256 := uint_toNat_lt i
  rw [fixedFloorIndex, uintOfNat_val (by omega)]
  rfl

/-- Actual storage-path reads, including a continuation into an element. -/
theorem fixedFloorVec_find {E U : Ty} {n : Nat} (B : List Int) (v : SVec E n)
    (hn : (n : Int) ∈ B) (i : PrimTy.uint.Denote) (q : Path E U) :
    (SVal.fixed (fixedFloorVec B v)).findM (.atF i q) =
      (SVal.fixed v).findM (.atF (fixedFloorIndex B i) q) := by
  simp only [SVal.findM, fixedFloorIndex_toNat, fixedFloorVec_slot B v hn]

/-- A finite block and retained exterior observations use one reconstructed vector. -/
theorem fixedFloorVec_block_reads {E : Ty} {n : Nat} (B : List Int) (v : SVec E n)
    (hn : (n : Int) ∈ B) (P : Option (SVal E) → Prop)
    (hi : ∀ k : Nat, k = 0 ∨ (k : Int) ∈ B → k < n → P (v.toList[k]?))
    (reads : List Nat) (hr : ∀ k ∈ reads, (k : Int) ∈ B) :
    (∀ k : Nat, k < n → P ((fixedFloorVec B v).toList[k]?)) ∧
      reads.map (fun k => (fixedFloorVec B v).toList[k]?) =
        reads.map (fun k => v.toList[k]?) := by
  constructor
  · intro k hk
    rw [fixedFloorVec_slot B v hn]
    exact hi (mxFloorIndex B k) (mxFloorIndex_point B k)
      ((mxFloorIndex_bounds B hn).2 hk)
  · apply List.map_congr_left
    intro k hk
    exact fixedFloorVec_at B v hn (hr k hk)

/-- Exact finite-instance boundary for all intrinsic fixed vectors of this length.
The exterior predicate sees precisely the retained optional element reads.
This does not recognize arbitrary intrinsic formulas or prove state agreement. -/
theorem fixedFloorVec_negative_iff {E : Ty} {n : Nat}
    (points : SVec E n → List Int) (reads : List Nat)
    (hn : ∀ v, (n : Int) ∈ points v)
    (hr : ∀ v k, k ∈ reads → (k : Int) ∈ points v)
    (P : Option (SVal E) → Prop) (Q : List (Option (SVal E)) → Prop) :
    (∀ v : SVec E n, (∀ k : Nat, k < n → P (v.toList[k]?)) →
      Q (reads.map fun k => v.toList[k]?)) ↔
    (∀ v : SVec E n, (∀ k : Nat, k = 0 ∨ (k : Int) ∈ points v →
      k < n → P (v.toList[k]?)) → Q (reads.map fun k => v.toList[k]?)) := by
  constructor
  · intro h v hi
    have hb : (∀ k : Nat, k < n → P ((fixedFloorVec (points v) v).toList[k]?)) ∧
        reads.map (fun k => (fixedFloorVec (points v) v).toList[k]?) =
          reads.map (fun k => v.toList[k]?) :=
      fixedFloorVec_block_reads (points v) v (hn v) P hi reads (hr v)
    have hq : Q (reads.map fun k => (fixedFloorVec (points v) v).toList[k]?) :=
      h (fixedFloorVec (points v) v) hb.1
    rw [hb.2] at hq
    exact hq
  · intro h v hi
    exact h v (fun k _ hk => hi k hk)

end Solidity.Decide
