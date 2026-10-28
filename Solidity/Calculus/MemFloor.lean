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
pass. It proves natural-index guard transfer and a length-guarded semantic
block reduction; it neither changes the heap nor claims intrinsic formula
guard transfer or `MxRel`.
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

/-- A retained lower guard operand transfers in both directions. -/
theorem mxFloorIndex_ge_iff (B : List Int) {n k : Nat} (hn : (n : Int) ∈ B) :
    n ≤ mxFloorIndex B k ↔ n ≤ k := by
  have hb := mxFloorIndex_bounds B (n := n) (k := k) hn
  omega

/-- Strict lower guards need the successor, not just the operand. -/
theorem mxFloorIndex_gt_iff (B : List Int) {n k : Nat} (hn : ((n + 1 : Nat) : Int) ∈ B) :
    n < mxFloorIndex B k ↔ n < k := by
  have hb := mxFloorIndex_ge_iff B (k := k) hn
  omega

/-- A non-strict upper guard likewise retains the successor. -/
theorem mxFloorIndex_le_iff (B : List Int) {n k : Nat} (hn : ((n + 1 : Nat) : Int) ∈ B) :
    mxFloorIndex B k ≤ n ↔ k ≤ n := by
  have hb := mxFloorIndex_bounds B (k := k) hn
  omega

/-- Equality guards retain both sides of their singleton region. -/
theorem mxFloorIndex_eq_iff (B : List Int) {n k : Nat}
    (hn : (n : Int) ∈ B) (hs : ((n + 1 : Nat) : Int) ∈ B) :
    mxFloorIndex B k = n ↔ k = n := by
  have hlo := mxFloorIndex_ge_iff B (k := k) hn
  have hhi := mxFloorIndex_le_iff B (k := k) hs
  omega

/-- A floor is the least index or one of the retained nonnegative points.
Negative breakpoints cannot become an extra natural instance. -/
theorem mxFloorIndex_point (B : List Int) (k : Nat) :
    mxFloorIndex B k = 0 ∨ (mxFloorIndex B k : Int) ∈ B := by
  have h0 : 0 ≤ floorIn 0 B (k : Int) := floorIn_ge_base 0 B _
  have he : (mxFloorIndex B k : Int) = floorIn 0 B (k : Int) := by
    unfold mxFloorIndex
    omega
  rcases floorIn_mem 0 B (k : Int) with h | h
  · left
    omega
  · right
    rw [he]
    exact h

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

/-- Finite instances reconstruct a length-guarded universal block.
`P` observes the optional primitive read itself, so halted reads are never
silently replaced by the primitive default. This is a semantic lemma, not
a recognizer for intrinsic formulas or a closer verdict. -/
theorem mxFloorRebuild_block {H : HTy} {R : RefTy} {q : PrimTy}
    (a : ArrTy R (.prim q)) (hok : mxArrOk a) (o : MObj H R) (B : List Int)
    (hn : ((MObj.elems a o).length : Int) ∈ B)
    (P : Option q.Denote → Prop)
    (hi : ∀ k : Nat, k = 0 ∨ (k : Int) ∈ B →
      k < (MObj.elems a o).length → P ((MObj.elems a o)[k]?)) :
    ∀ k : Nat, k < (MObj.elems a (mxFloorRebuild a hok o B)).length →
      P ((MObj.elems a (mxFloorRebuild a hok o B))[k]?) := by
  intro k hk
  rw [mxFloorRebuild_len] at hk
  rw [mxFloorRebuild_slot a hok o B hn]
  exact hi (mxFloorIndex B k) (mxFloorIndex_point B k)
    ((mxFloorIndex_bounds B hn).2 hk)

/-- A simultaneous block and exterior-observation reconstruction. The
caller keeps every successful ground index and the length; the same
object then realizes the block and every exterior optional read together.
This is the object-level refutation interface required by a later scoped
preparation, including written-memory hashing. It does not rebuild a heap
or establish a relation between intrinsic formula states. -/
theorem mxFloorRebuild_block_reads {H : HTy} {R : RefTy} {q : PrimTy}
    (a : ArrTy R (.prim q)) (hok : mxArrOk a) (o : MObj H R) (B : List Int)
    (hn : ((MObj.elems a o).length : Int) ∈ B)
    (P : Option q.Denote → Prop)
    (hi : ∀ k : Nat, k = 0 ∨ (k : Int) ∈ B →
      k < (MObj.elems a o).length → P ((MObj.elems a o)[k]?))
    (reads : List Nat) (hr : ∀ k ∈ reads, (k : Int) ∈ B) :
    (∀ k : Nat, k < (MObj.elems a (mxFloorRebuild a hok o B)).length →
      P ((MObj.elems a (mxFloorRebuild a hok o B))[k]?)) ∧
    reads.map (fun k => (MObj.elems a (mxFloorRebuild a hok o B))[k]?) =
      reads.map (fun k => (MObj.elems a o)[k]?) := by
  refine ⟨mxFloorRebuild_block a hok o B hn P hi, ?_⟩
  apply List.map_congr_left
  intro k hk
  exact mxFloorRebuild_at a hok o B hn (hr k hk)

/-- Exact finite-instance reduction over one fresh primitive object.
The exterior observation can depend on its length and every listed ground
optional read. The index-set builder is allowed to use the object, but
must retain that object's length and all exterior reads. No decision or
recognition procedure is hidden in this theorem. -/
theorem mxFloorRebuild_negative_iff {H : HTy} {R : RefTy} {q : PrimTy}
    (a : ArrTy R (.prim q)) (hok : mxArrOk a)
    (points : MObj H R → List Int) (reads : List Nat)
    (hn : ∀ o, ((MObj.elems a o).length : Int) ∈ points o)
    (hr : ∀ o k, k ∈ reads → (k : Int) ∈ points o)
    (P : Nat → Option q.Denote → Prop)
    (Q : Nat → List (Option q.Denote) → Prop) :
    (∀ o : MObj H R,
      (∀ k : Nat, k < (MObj.elems a o).length →
        P (MObj.elems a o).length ((MObj.elems a o)[k]?)) →
      Q (MObj.elems a o).length (reads.map fun k => (MObj.elems a o)[k]?)) ↔
    (∀ o : MObj H R,
      (∀ k : Nat, k = 0 ∨ (k : Int) ∈ points o →
        k < (MObj.elems a o).length →
        P (MObj.elems a o).length ((MObj.elems a o)[k]?)) →
      Q (MObj.elems a o).length (reads.map fun k => (MObj.elems a o)[k]?)) := by
  constructor
  · intro h o hi
    have hb := mxFloorRebuild_block_reads a hok o (points o) (hn o)
      (P (MObj.elems a o).length) hi reads (hr o)
    have hall : ∀ k : Nat,
        k < (MObj.elems a (mxFloorRebuild a hok o (points o))).length →
        P (MObj.elems a (mxFloorRebuild a hok o (points o))).length
          ((MObj.elems a (mxFloorRebuild a hok o (points o)))[k]?) := by
      rw [mxFloorRebuild_len]
      simpa only [mxFloorRebuild_len] using hb.1
    have hq := h (mxFloorRebuild a hok o (points o)) hall
    rw [mxFloorRebuild_len, hb.2] at hq
    exact hq
  · intro h o hi
    exact h o (fun k _ hk => hi k hk)

#print axioms mxFloorRebuild_negative_iff

#print axioms mxFloorIndex_eq_iff
#print axioms mxFloorRebuild_block
#print axioms mxFloorRebuild_block_reads

#print axioms mxFloorRebuild_slot
#print axioms mxFloorRebuild_fill

end Solidity.Decide
