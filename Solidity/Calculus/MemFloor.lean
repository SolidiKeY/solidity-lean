import Solidity.Calculus.MemSwap
import Solidity.Calculus.FloorRegion

/-!
# Same-length reconstruction of primitive memory arrays

The object-level reconstruction needed before instantiating a negative
memory-array block. The length belongs to the floor set: without that
premise, flooring an out-of-bounds index can turn a halted read into a word.
Unlike storage reconstruction, this construction keeps the original length
and therefore keeps the strict `2^256` memory bound.

This is an additive semantic interface, not a negative-block preparation
pass. It neither changes the heap nor claims guard transfer or `MxRel`.
-/

namespace Solidity.Decide

/-- A natural index floored at the existing integer breakpoints. -/
def mxFloorIndex (B : List Int) (k : Nat) : Nat :=
  (floorIn 0 B (k : Int)).toNat

/-- Flooring stays below the original index. -/
theorem mxFloorIndex_le (B : List Int) (k : Nat) : mxFloorIndex B k ≤ k := by
  have h0 : 0 ≤ floorIn 0 B (k : Int) := floorIn_ge_base 0 B _
  have h1 : floorIn 0 B (k : Int) ≤ (k : Int) := floorIn_le 0 B (by omega)
  unfold mxFloorIndex
  omega

/-- Flooring is monotone, including beyond an array's length. -/
theorem mxFloorIndex_mono (B : List Int) {i j : Nat} (h : i ≤ j) :
    mxFloorIndex B i ≤ mxFloorIndex B j := by
  have h0 : 0 ≤ floorIn 0 B (i : Int) := floorIn_ge_base 0 B _
  have h1 : 0 ≤ floorIn 0 B (j : Int) := floorIn_ge_base 0 B _
  have h2 : floorIn 0 B (i : Int) ≤ floorIn 0 B (j : Int) :=
    floorIn_mono 0 B (by omega) (by omega)
  unfold mxFloorIndex
  omega

/-- Every retained natural breakpoint is a fixed point. -/
theorem mxFloorIndex_fix (B : List Int) {k : Nat} (h : (k : Int) ∈ B) :
    mxFloorIndex B k = k := by
  unfold mxFloorIndex
  rw [floorIn_fix 0 B h (by omega)]
  rfl

/-- Including the length preserves definedness in both directions. -/
theorem mxFloorIndex_bounds (B : List Int) {n k : Nat} (hn : (n : Int) ∈ B) :
    mxFloorIndex B k < n ↔ k < n := by
  constructor
  · intro hk
    apply Classical.byContradiction
    intro h
    have hm : mxFloorIndex B n ≤ mxFloorIndex B k := mxFloorIndex_mono B (by omega)
    rw [mxFloorIndex_fix B hn] at hm
    omega
  · intro hk
    have hf : mxFloorIndex B k ≤ k := mxFloorIndex_le B k
    omega

/-- Rebuild a primitive array at the floors, keeping its exact length and
array kind. No reference-valued object or given-heap binder is rebuilt. -/
def mxFloorRebuild {H : HTy} {R : RefTy} {q : PrimTy}
    (a : ArrTy R (.prim q)) (hok : mxArrOk a) (o : MObj H R) (B : List Int) : MObj H R :=
  mxMk (mxFillN a o)
    (List.ofFn fun i : Fin (MObj.elems a o).length =>
      (MObj.elems a o)[mxFloorIndex B i.val]'(by
        have h : mxFloorIndex B i.val ≤ i.val := mxFloorIndex_le B i.val
        omega))
    a hok (by rw [List.length_ofFn]; exact mxFillN_len a hok o)

/-- The reconstruction's elements, without exposing array-kind casts. -/
theorem mxFloorRebuild_elems {H : HTy} {R : RefTy} {q : PrimTy}
    (a : ArrTy R (.prim q)) (hok : mxArrOk a) (o : MObj H R) (B : List Int) :
    MObj.elems a (mxFloorRebuild a hok o B) =
      List.ofFn (fun i : Fin (MObj.elems a o).length =>
        (MObj.elems a o)[mxFloorIndex B i.val]'(by
          have h : mxFloorIndex B i.val ≤ i.val := mxFloorIndex_le B i.val
          omega)) := by
  unfold mxFloorRebuild
  rw [mxElems_mk]

/-- The length is unchanged, including zero and fixed-array lengths. -/
theorem mxFloorRebuild_len {H : HTy} {R : RefTy} {q : PrimTy}
    (a : ArrTy R (.prim q)) (hok : mxArrOk a) (o : MObj H R) (B : List Int) :
    (MObj.elems a (mxFloorRebuild a hok o B)).length = (MObj.elems a o).length := by
  rw [mxFloorRebuild_elems, List.length_ofFn]

/-- Exact optional reads: words below the length and `none` beyond it.
The length breakpoint is essential for the latter case. -/
theorem mxFloorRebuild_slot {H : HTy} {R : RefTy} {q : PrimTy}
    (a : ArrTy R (.prim q)) (hok : mxArrOk a) (o : MObj H R) (B : List Int)
    (hn : ((MObj.elems a o).length : Int) ∈ B) (k : Nat) :
    (MObj.elems a (mxFloorRebuild a hok o B))[k]? =
      (MObj.elems a o)[mxFloorIndex B k]? := by
  rw [mxFloorRebuild_elems, List.getElem?_ofFn]
  by_cases hk : k < (MObj.elems a o).length
  · have hf : mxFloorIndex B k < (MObj.elems a o).length :=
      (mxFloorIndex_bounds B hn).2 hk
    simp only [hk, dite_true, List.getElem?_eq_getElem hf]
  · have hf : (MObj.elems a o).length ≤ mxFloorIndex B k := by
      have hb := mxFloorIndex_bounds B (k := k) hn
      omega
    rw [dif_neg hk, List.getElem?_eq_none hf]

/-- Reads at retained indices agree, even where they halt. -/
theorem mxFloorRebuild_at {H : HTy} {R : RefTy} {q : PrimTy}
    (a : ArrTy R (.prim q)) (hok : mxArrOk a) (o : MObj H R) (B : List Int)
    (hn : ((MObj.elems a o).length : Int) ∈ B) {k : Nat} (hk : (k : Int) ∈ B) :
    (MObj.elems a (mxFloorRebuild a hok o B))[k]? = (MObj.elems a o)[k]? := by
  rw [mxFloorRebuild_slot a hok o B hn, mxFloorIndex_fix B hk]

/-- The length word supplied to `MxMap` is unchanged. -/
theorem mxFloorRebuild_fillN {H : HTy} {R : RefTy} {q : PrimTy}
    (a : ArrTy R (.prim q)) (hok : mxArrOk a) (o : MObj H R) (B : List Int) :
    mxFillN a (mxFloorRebuild a hok o B) = mxFillN a o := by
  unfold mxFillN
  rw [mxFloorRebuild_len]

/-- The existing `MxMap` read-table filling interface is preserved when
all successful index evaluations land in the retained set. This includes
out-of-bounds indices; their optional reads remain `none`. -/
theorem mxFloorRebuild_fill {C : Contract} {Γ Δ : Ctx} {θ : MxMap C Γ Δ} {q : PrimTy}
    (τ : State C Γ) {R : RefTy} (a : ArrTy R (.prim q)) (hok : mxArrOk a)
    (ps : List (MxIx θ)) (o : MObj τ.H R) (B : List Int)
    (hn : ((MObj.elems a o).length : Int) ∈ B)
    (hs : ∀ (j : Fin ps.length) (k : PrimTy.uint.Denote),
      (ps.get j).e.eval τ = some k → (k.1.toNat : Int) ∈ B) :
    mxFill τ a ps (mxFloorRebuild a hok o B) = mxFill τ a ps o := by
  funext j
  unfold mxFill
  cases he : (ps.get j).e.eval τ with
  | none => rfl
  | some k => exact congrArg (fun x => x.getD (PrimTy.dflt q)) (mxFloorRebuild_at a hok o B hn (hs j k he))

#print axioms mxFloorRebuild_slot
#print axioms mxFloorRebuild_fill

end Solidity.Decide
