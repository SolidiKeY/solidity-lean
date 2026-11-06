import Solidity.Backend.StorageOps.PushTransport

/-! Actual numeric lifecycle operations, current-header generated touched
sets, disjoint commutation and finite transport. Existing WordStore/Loc update
interfaces only; no alternative IR/state or Source/world closure is defined. -/
namespace Solidity.Backend.StorageOps.NumericCommutation
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Header read plus actual writes. Failure touches ONLY the header; it does
not require a fictitious unexecuted reset location or new admission bound. -/
def pushTouches (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (initial : WordStore) : List Solidity.Storage.Loc :=
  let length := LifecycleNumeric.headerLength N hash base initial
  if length + 1 < 2 ^ 256 then [base, .data base length] else [base]

def pushUpdates (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (initial : WordStore) : List (Solidity.Storage.Loc × Semantics.Word) :=
  let length := LifecycleNumeric.headerLength N hash base initial
  if room : length + 1 < 2 ^ 256 then
    [(.data base length, ClearDemands.zero), (base, lengthWord (length + 1) room)] else []

/-- Empty pop reads only the header; successful pop also clears its actual
last-live element. Retained extent is never used as a traversal bound. -/
def popTouches (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (initial : WordStore) : List Solidity.Storage.Loc :=
  let length := LifecycleNumeric.headerLength N hash base initial
  if 0 < length then [base, .data base (length - 1)] else [base]

private def twoWrites (m : WordStore) (a0 : Nat) (v0 : Semantics.Word) (a1 : Nat) (v1 : Semantics.Word) : WordStore :=
  writeWord (writeWord m a0 v0) a1 v1

private theorem two_commute (m : WordStore) (a0 a1 b0 b1 : Nat) (va0 va1 vb0 vb1 : Semantics.Word)
    (separate : ∀ a ∈ [a0,a1], ∀ b ∈ [b0,b1], a ≠ b) :
    twoWrites (twoWrites m a0 va0 a1 va1) b0 vb0 b1 vb1 =
      twoWrites (twoWrites m b0 vb0 b1 vb1) a0 va0 a1 va1 := by
  have h00 := separate a0 List.mem_cons_self b0 List.mem_cons_self
  have h01 := separate a0 List.mem_cons_self b1 (List.mem_cons_of_mem _ List.mem_cons_self)
  have h10 := separate a1 (List.mem_cons_of_mem _ List.mem_cons_self) b0 List.mem_cons_self
  have h11 := separate a1 (List.mem_cons_of_mem _ List.mem_cons_self) b1 (List.mem_cons_of_mem _ List.mem_cons_self)
  funext k
  by_cases hit1 : k = a1
  · subst k
    simp only [twoWrites, writeWord, if_neg h11, if_neg h10, if_true]
  · by_cases hit0 : k = a0
    · subst k
      simp only [twoWrites, writeWord, if_neg h01, if_neg h00, if_neg hit1, if_true]
    · simp only [twoWrites, writeWord, if_neg hit1, if_neg hit0]

private theorem header_two {N : Nat} (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (m : WordStore) (a0 a1 : Nat) (v0 v1 : Semantics.Word)
    (outside0 : base.word N hash ≠ a0) (outside1 : base.word N hash ≠ a1) :
    LifecycleNumeric.headerLength N hash base (twoWrites m a0 v0 a1 v1) =
      LifecycleNumeric.headerLength N hash base m := by
  simp only [LifecycleNumeric.headerLength, twoWrites, writeWord, if_neg outside0, if_neg outside1]

private theorem push_framed {N : Nat} (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (before after : WordStore)
    (same : LifecycleNumeric.headerLength N hash base after = LifecycleNumeric.headerLength N hash base before) :
    LifecycleNumeric.pushPrimitive N hash base after =
      if room : LifecycleNumeric.headerLength N hash base before + 1 < 2 ^ 256 then
        some (twoWrites after ((Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base before)).word N hash)
          ClearDemands.zero (base.word N hash)
          (lengthWord (LifecycleNumeric.headerLength N hash base before + 1) room)) else none := by
  unfold LifecycleNumeric.pushPrimitive
  simp only [same, twoWrites]

private theorem push_push_physical {N : Nat} (hash : Solidity.Storage.Pre → Nat)
    (a b : Solidity.Storage.Loc) (m : WordStore)
    (headers : a.word N hash ≠ b.word N hash)
    (leftFrame : LifecycleNumeric.headerLength N hash a m + 1 < 2 ^ 256 →
      b.word N hash ≠ (Solidity.Storage.Loc.data a (LifecycleNumeric.headerLength N hash a m)).word N hash)
    (rightFrame : LifecycleNumeric.headerLength N hash b m + 1 < 2 ^ 256 →
      a.word N hash ≠ (Solidity.Storage.Loc.data b (LifecycleNumeric.headerLength N hash b m)).word N hash)
    (elements : LifecycleNumeric.headerLength N hash a m + 1 < 2 ^ 256 →
      LifecycleNumeric.headerLength N hash b m + 1 < 2 ^ 256 →
      (Solidity.Storage.Loc.data a (LifecycleNumeric.headerLength N hash a m)).word N hash ≠
        (Solidity.Storage.Loc.data b (LifecycleNumeric.headerLength N hash b m)).word N hash) :
    (LifecycleNumeric.pushPrimitive N hash a m).bind (LifecycleNumeric.pushPrimitive N hash b) =
      (LifecycleNumeric.pushPrimitive N hash b m).bind (LifecycleNumeric.pushPrimitive N hash a) := by
  by_cases roomA : LifecycleNumeric.headerLength N hash a m + 1 < 2 ^ 256
  · let updateA := fun initial => twoWrites initial
      ((Solidity.Storage.Loc.data a (LifecycleNumeric.headerLength N hash a m)).word N hash) ClearDemands.zero
      (a.word N hash) (lengthWord (LifecycleNumeric.headerLength N hash a m + 1) roomA)
    have aFirst : LifecycleNumeric.pushPrimitive N hash a m = some (updateA m) := by
      exact dif_pos roomA
    have frameB : LifecycleNumeric.headerLength N hash b (updateA m) = LifecycleNumeric.headerLength N hash b m :=
      header_two hash b m _ _ _ _ (leftFrame roomA) (Ne.symm headers)
    by_cases roomB : LifecycleNumeric.headerLength N hash b m + 1 < 2 ^ 256
    · let updateB := fun initial => twoWrites initial
        ((Solidity.Storage.Loc.data b (LifecycleNumeric.headerLength N hash b m)).word N hash) ClearDemands.zero
        (b.word N hash) (lengthWord (LifecycleNumeric.headerLength N hash b m + 1) roomB)
      have bFirst : LifecycleNumeric.pushPrimitive N hash b m = some (updateB m) := by exact dif_pos roomB
      have frameA : LifecycleNumeric.headerLength N hash a (updateB m) = LifecycleNumeric.headerLength N hash a m :=
        header_two hash a m _ _ _ _ (rightFrame roomB) headers
      have bAfter : LifecycleNumeric.pushPrimitive N hash b (updateA m) = some (updateB (updateA m)) := by
        rw [push_framed hash b m (updateA m) frameB, dif_pos roomB]
      have aAfter : LifecycleNumeric.pushPrimitive N hash a (updateB m) = some (updateA (updateB m)) := by
        rw [push_framed hash a m (updateB m) frameA, dif_pos roomA]
      simp only [aFirst, bFirst, Option.bind_some, bAfter, aAfter]
      apply congrArg some
      apply two_commute
      intro x insideX y insideY
      simp only [List.mem_cons, List.not_mem_nil, or_false] at insideX insideY
      rcases insideX with rfl | rfl <;> rcases insideY with rfl | rfl
      · exact elements roomA roomB
      · exact Ne.symm (leftFrame roomA)
      · exact rightFrame roomB
      · exact headers
    · have bFirst : LifecycleNumeric.pushPrimitive N hash b m = none := dif_neg roomB
      have bAfter : LifecycleNumeric.pushPrimitive N hash b (updateA m) = none := by
        rw [push_framed hash b m (updateA m) frameB, dif_neg roomB]
      rw [aFirst, bFirst, Option.bind_some, Option.bind_none, bAfter]
  · have aFirst : LifecycleNumeric.pushPrimitive N hash a m = none := dif_neg roomA
    by_cases roomB : LifecycleNumeric.headerLength N hash b m + 1 < 2 ^ 256
    · let updateB := fun initial => twoWrites initial
        ((Solidity.Storage.Loc.data b (LifecycleNumeric.headerLength N hash b m)).word N hash) ClearDemands.zero
        (b.word N hash) (lengthWord (LifecycleNumeric.headerLength N hash b m + 1) roomB)
      have bFirst : LifecycleNumeric.pushPrimitive N hash b m = some (updateB m) := dif_pos roomB
      have frameA : LifecycleNumeric.headerLength N hash a (updateB m) = LifecycleNumeric.headerLength N hash a m :=
        header_two hash a m _ _ _ _ (rightFrame roomB) headers
      have aAfter : LifecycleNumeric.pushPrimitive N hash a (updateB m) = none := by
        rw [push_framed hash a m (updateB m) frameA, dif_neg roomA]
      rw [aFirst, bFirst, Option.bind_none, Option.bind_some, aAfter]
    · have bFirst : LifecycleNumeric.pushPrimitive N hash b m = none := dif_neg roomB
      rw [aFirst, bFirst, Option.bind_none, Option.bind_none]

private theorem header_bound {N : Nat} (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (m : WordStore) : LifecycleNumeric.headerLength N hash base m < 2 ^ 256 := by
  have bound := (m (base.word N hash)).property
  simp only [PrimTy.inRange, decide_eq_true_eq] at bound
  unfold LifecycleNumeric.headerLength
  omega

def popUpdates (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (initial : WordStore) : List (Solidity.Storage.Loc × Semantics.Word) :=
  let length := LifecycleNumeric.headerLength N hash base initial
  if 0 < length then
    [(.data base (length - 1), ClearDemands.zero),
      (base, lengthWord (length - 1) (by have bound := header_bound (N := N) hash base initial; omega))] else []

private theorem pop_framed {N : Nat} (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (before after : WordStore)
    (same : LifecycleNumeric.headerLength N hash base after = LifecycleNumeric.headerLength N hash base before) :
    PrimitivePop.execute N hash base after =
      if live : 0 < LifecycleNumeric.headerLength N hash base before then
        some (twoWrites after ((Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base before - 1)).word N hash)
          ClearDemands.zero (base.word N hash)
          (lengthWord (LifecycleNumeric.headerLength N hash base before - 1)
            (by have bound := header_bound (N := N) hash base before; omega))) else none := by
  unfold PrimitivePop.execute
  simp only [same, twoWrites]

private theorem push_pop_physical {N : Nat} (hash : Solidity.Storage.Pre → Nat)
    (a b : Solidity.Storage.Loc) (m : WordStore)
    (headers : a.word N hash ≠ b.word N hash)
    (leftFrame : LifecycleNumeric.headerLength N hash a m + 1 < 2 ^ 256 →
      b.word N hash ≠ (Solidity.Storage.Loc.data a (LifecycleNumeric.headerLength N hash a m)).word N hash)
    (rightFrame : 0 < LifecycleNumeric.headerLength N hash b m →
      a.word N hash ≠ (Solidity.Storage.Loc.data b (LifecycleNumeric.headerLength N hash b m - 1)).word N hash)
    (elements : LifecycleNumeric.headerLength N hash a m + 1 < 2 ^ 256 →
      0 < LifecycleNumeric.headerLength N hash b m →
      (Solidity.Storage.Loc.data a (LifecycleNumeric.headerLength N hash a m)).word N hash ≠
        (Solidity.Storage.Loc.data b (LifecycleNumeric.headerLength N hash b m - 1)).word N hash) :
    (LifecycleNumeric.pushPrimitive N hash a m).bind (PrimitivePop.execute N hash b) =
      (PrimitivePop.execute N hash b m).bind (LifecycleNumeric.pushPrimitive N hash a) := by
  by_cases roomA : LifecycleNumeric.headerLength N hash a m + 1 < 2 ^ 256
  · let updateA := fun initial => twoWrites initial
      ((Solidity.Storage.Loc.data a (LifecycleNumeric.headerLength N hash a m)).word N hash) ClearDemands.zero
      (a.word N hash) (lengthWord (LifecycleNumeric.headerLength N hash a m + 1) roomA)
    have aFirst : LifecycleNumeric.pushPrimitive N hash a m = some (updateA m) := by
      exact dif_pos roomA
    have frameB : LifecycleNumeric.headerLength N hash b (updateA m) = LifecycleNumeric.headerLength N hash b m :=
      header_two hash b m _ _ _ _ (leftFrame roomA) (Ne.symm headers)
    by_cases roomB : 0 < LifecycleNumeric.headerLength N hash b m
    · let updateB := fun initial => twoWrites initial
        ((Solidity.Storage.Loc.data b (LifecycleNumeric.headerLength N hash b m - 1)).word N hash) ClearDemands.zero
        (b.word N hash) (lengthWord (LifecycleNumeric.headerLength N hash b m - 1) (by have bound := header_bound (N := N) hash b m; omega))
      have bFirst : PrimitivePop.execute N hash b m = some (updateB m) := by exact dif_pos roomB
      have frameA : LifecycleNumeric.headerLength N hash a (updateB m) = LifecycleNumeric.headerLength N hash a m :=
        header_two hash a m _ _ _ _ (rightFrame roomB) headers
      have bAfter : PrimitivePop.execute N hash b (updateA m) = some (updateB (updateA m)) := by
        rw [pop_framed hash b m (updateA m) frameB, dif_pos roomB]
      have aAfter : LifecycleNumeric.pushPrimitive N hash a (updateB m) = some (updateA (updateB m)) := by
        rw [push_framed hash a m (updateB m) frameA, dif_pos roomA]
      simp only [aFirst, bFirst, Option.bind_some, bAfter, aAfter]
      apply congrArg some
      apply two_commute
      intro x insideX y insideY
      simp only [List.mem_cons, List.not_mem_nil, or_false] at insideX insideY
      rcases insideX with rfl | rfl <;> rcases insideY with rfl | rfl
      · exact elements roomA roomB
      · exact Ne.symm (leftFrame roomA)
      · exact rightFrame roomB
      · exact headers
    · have bFirst : PrimitivePop.execute N hash b m = none := dif_neg roomB
      have bAfter : PrimitivePop.execute N hash b (updateA m) = none := by
        rw [pop_framed hash b m (updateA m) frameB, dif_neg roomB]
      rw [aFirst, bFirst, Option.bind_some, Option.bind_none, bAfter]
  · have aFirst : LifecycleNumeric.pushPrimitive N hash a m = none := dif_neg roomA
    by_cases roomB : 0 < LifecycleNumeric.headerLength N hash b m
    · let updateB := fun initial => twoWrites initial
        ((Solidity.Storage.Loc.data b (LifecycleNumeric.headerLength N hash b m - 1)).word N hash) ClearDemands.zero
        (b.word N hash) (lengthWord (LifecycleNumeric.headerLength N hash b m - 1) (by have bound := header_bound (N := N) hash b m; omega))
      have bFirst : PrimitivePop.execute N hash b m = some (updateB m) := dif_pos roomB
      have frameA : LifecycleNumeric.headerLength N hash a (updateB m) = LifecycleNumeric.headerLength N hash a m :=
        header_two hash a m _ _ _ _ (rightFrame roomB) headers
      have aAfter : LifecycleNumeric.pushPrimitive N hash a (updateB m) = none := by
        rw [push_framed hash a m (updateB m) frameA, dif_neg roomA]
      rw [aFirst, bFirst, Option.bind_none, Option.bind_some, aAfter]
    · have bFirst : PrimitivePop.execute N hash b m = none := dif_neg roomB
      rw [aFirst, bFirst, Option.bind_none, Option.bind_none]

private theorem pop_pop_physical {N : Nat} (hash : Solidity.Storage.Pre → Nat)
    (a b : Solidity.Storage.Loc) (m : WordStore)
    (headers : a.word N hash ≠ b.word N hash)
    (leftFrame : 0 < LifecycleNumeric.headerLength N hash a m →
      b.word N hash ≠ (Solidity.Storage.Loc.data a (LifecycleNumeric.headerLength N hash a m - 1)).word N hash)
    (rightFrame : 0 < LifecycleNumeric.headerLength N hash b m →
      a.word N hash ≠ (Solidity.Storage.Loc.data b (LifecycleNumeric.headerLength N hash b m - 1)).word N hash)
    (elements : 0 < LifecycleNumeric.headerLength N hash a m →
      0 < LifecycleNumeric.headerLength N hash b m →
      (Solidity.Storage.Loc.data a (LifecycleNumeric.headerLength N hash a m - 1)).word N hash ≠
        (Solidity.Storage.Loc.data b (LifecycleNumeric.headerLength N hash b m - 1)).word N hash) :
    (PrimitivePop.execute N hash a m).bind (PrimitivePop.execute N hash b) =
      (PrimitivePop.execute N hash b m).bind (PrimitivePop.execute N hash a) := by
  by_cases roomA : 0 < LifecycleNumeric.headerLength N hash a m
  · let updateA := fun initial => twoWrites initial
      ((Solidity.Storage.Loc.data a (LifecycleNumeric.headerLength N hash a m - 1)).word N hash) ClearDemands.zero
      (a.word N hash) (lengthWord (LifecycleNumeric.headerLength N hash a m - 1) (by have bound := header_bound (N := N) hash a m; omega))
    have aFirst : PrimitivePop.execute N hash a m = some (updateA m) := by
      exact dif_pos roomA
    have frameB : LifecycleNumeric.headerLength N hash b (updateA m) = LifecycleNumeric.headerLength N hash b m :=
      header_two hash b m _ _ _ _ (leftFrame roomA) (Ne.symm headers)
    by_cases roomB : 0 < LifecycleNumeric.headerLength N hash b m
    · let updateB := fun initial => twoWrites initial
        ((Solidity.Storage.Loc.data b (LifecycleNumeric.headerLength N hash b m - 1)).word N hash) ClearDemands.zero
        (b.word N hash) (lengthWord (LifecycleNumeric.headerLength N hash b m - 1) (by have bound := header_bound (N := N) hash b m; omega))
      have bFirst : PrimitivePop.execute N hash b m = some (updateB m) := by exact dif_pos roomB
      have frameA : LifecycleNumeric.headerLength N hash a (updateB m) = LifecycleNumeric.headerLength N hash a m :=
        header_two hash a m _ _ _ _ (rightFrame roomB) headers
      have bAfter : PrimitivePop.execute N hash b (updateA m) = some (updateB (updateA m)) := by
        rw [pop_framed hash b m (updateA m) frameB, dif_pos roomB]
      have aAfter : PrimitivePop.execute N hash a (updateB m) = some (updateA (updateB m)) := by
        rw [pop_framed hash a m (updateB m) frameA, dif_pos roomA]
      simp only [aFirst, bFirst, Option.bind_some, bAfter, aAfter]
      apply congrArg some
      apply two_commute
      intro x insideX y insideY
      simp only [List.mem_cons, List.not_mem_nil, or_false] at insideX insideY
      rcases insideX with rfl | rfl <;> rcases insideY with rfl | rfl
      · exact elements roomA roomB
      · exact Ne.symm (leftFrame roomA)
      · exact rightFrame roomB
      · exact headers
    · have bFirst : PrimitivePop.execute N hash b m = none := dif_neg roomB
      have bAfter : PrimitivePop.execute N hash b (updateA m) = none := by
        rw [pop_framed hash b m (updateA m) frameB, dif_neg roomB]
      rw [aFirst, bFirst, Option.bind_some, Option.bind_none, bAfter]
  · have aFirst : PrimitivePop.execute N hash a m = none := dif_neg roomA
    by_cases roomB : 0 < LifecycleNumeric.headerLength N hash b m
    · let updateB := fun initial => twoWrites initial
        ((Solidity.Storage.Loc.data b (LifecycleNumeric.headerLength N hash b m - 1)).word N hash) ClearDemands.zero
        (b.word N hash) (lengthWord (LifecycleNumeric.headerLength N hash b m - 1) (by have bound := header_bound (N := N) hash b m; omega))
      have bFirst : PrimitivePop.execute N hash b m = some (updateB m) := dif_pos roomB
      have frameA : LifecycleNumeric.headerLength N hash a (updateB m) = LifecycleNumeric.headerLength N hash a m :=
        header_two hash a m _ _ _ _ (rightFrame roomB) headers
      have aAfter : PrimitivePop.execute N hash a (updateB m) = none := by
        rw [pop_framed hash a m (updateB m) frameA, dif_neg roomA]
      rw [aFirst, bFirst, Option.bind_none, Option.bind_some, aAfter]
    · have bFirst : PrimitivePop.execute N hash b m = none := dif_neg roomB
      rw [aFirst, bFirst, Option.bind_none, Option.bind_none]

private theorem header_member (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (m : WordStore) :
    base ∈ pushTouches N hash base m := by
  dsimp only [pushTouches]
  split <;> exact List.mem_cons_self

private theorem element_member {N : Nat} (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (m : WordStore)
    (room : LifecycleNumeric.headerLength N hash base m + 1 < 2 ^ 256) :
    Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base m) ∈ pushTouches N hash base m := by
  rw [pushTouches, if_pos room]
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- Actual current-header pushes commute including BOTH failure outcomes.
Only actual generated read/write touches are covered/separated under the
existing PUBLIC per-run region premise, never global hash injectivity. -/
theorem push_push {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (a b : Solidity.Storage.Loc) (m : WordStore)
    (covered : ∀ l ∈ pushTouches N hash a m ++ pushTouches N hash b m, l ∈ locations)
    (separate : ∀ x ∈ pushTouches N hash a m, ∀ y ∈ pushTouches N hash b m, x ≠ y) :
    (LifecycleNumeric.pushPrimitive N hash a m).bind (LifecycleNumeric.pushPrimitive N hash b) =
      (LifecycleNumeric.pushPrimitive N hash b m).bind (LifecycleNumeric.pushPrimitive N hash a) := by
  have ha := header_member N hash a m
  have hb := header_member N hash b m
  have ne : ∀ x ∈ pushTouches N hash a m, ∀ y ∈ pushTouches N hash b m, x.word N hash ≠ y.word N hash := by
    intro x insideX y insideY same
    exact separate x insideX y insideY (run.word_inj
      (covered x (List.mem_append.mpr (Or.inl insideX))) (covered y (List.mem_append.mpr (Or.inr insideY))) same)
  apply push_push_physical hash a b m (ne a ha b hb)
  · intro room; exact Ne.symm (ne _ (element_member hash a m room) b hb)
  · intro room; exact ne a ha _ (element_member hash b m room)
  · intro roomA roomB; exact ne _ (element_member hash a m roomA) _ (element_member hash b m roomB)

theorem update_touched (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc)
    (m : WordStore) (op : Solidity.Storage.Loc × Semantics.Word) (member : op ∈ pushUpdates N hash base m) :
    op.1 ∈ pushTouches N hash base m := by
  dsimp only [pushUpdates] at member
  split at member
  next room =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rw [pushTouches, if_pos room]
    rcases member with rfl | rfl
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_self
  next full => cases member

/-- Fold equality is derived from the actual operation result, not assumed as
an abstract operation certificate. Failed operations produce no final store. -/
theorem push_realized (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc)
    (initial final : WordStore) (executed : LifecycleNumeric.pushPrimitive N hash base initial = some final) :
    final = (pushUpdates N hash base initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial := by
  dsimp only [LifecycleNumeric.pushPrimitive] at executed
  split at executed
  next room =>
    cases executed
    simp only [pushUpdates, dif_pos room, List.foldl_cons, List.foldl_nil]
  next full => cases executed

/-- Actual generated-write transport, reusing the owner's transport_sequence.
The touched certificate includes precisely the success/failure header branch. -/
theorem push_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (base : Solidity.Storage.Loc)
    (store : Store) (initial final : WordStore) (transport : Transport N hash locations store initial)
    (executed : LifecycleNumeric.pushPrimitive N hash base initial = some final)
    (covered : ∀ l ∈ pushTouches N hash base initial, l ∈ locations) :
    Transport N hash locations
      ((pushUpdates N hash base initial).foldl (fun w op => Representation.write w op.1 op.2) store) final := by
  rw [push_realized N hash base initial final executed]
  apply transport_sequence run transport
  intro op member
  exact covered op.1 (update_touched N hash base initial op member)

/-- Sequential actual operations transport their OWN generated accesses. No
world rollback or immutable source-state hypothesis is inferred. -/
theorem push_sequence_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (a b : Solidity.Storage.Loc)
    (store : Store) (initial middle final : WordStore) (transport : Transport N hash locations store initial)
    (first : LifecycleNumeric.pushPrimitive N hash a initial = some middle)
    (second : LifecycleNumeric.pushPrimitive N hash b middle = some final)
    (coveredA : ∀ l ∈ pushTouches N hash a initial, l ∈ locations)
    (coveredB : ∀ l ∈ pushTouches N hash b middle, l ∈ locations) :
    Transport N hash locations
      ((pushUpdates N hash b middle).foldl (fun w op => Representation.write w op.1 op.2)
        ((pushUpdates N hash a initial).foldl (fun w op => Representation.write w op.1 op.2) store)) final :=
  push_transport run b _ middle final (push_transport run a store initial middle transport first coveredA) second coveredB

/-- The second operation's actual header, touch set and update payload are
stable across a disjoint first push. This is proved, never a premise. -/
theorem disjoint_frame {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (a b : Solidity.Storage.Loc) (initial middle : WordStore)
    (executed : LifecycleNumeric.pushPrimitive N hash a initial = some middle)
    (covered : ∀ l ∈ pushTouches N hash a initial ++ pushTouches N hash b initial, l ∈ locations)
    (separate : ∀ x ∈ pushTouches N hash a initial, ∀ y ∈ pushTouches N hash b initial, x ≠ y) :
    LifecycleNumeric.headerLength N hash b middle = LifecycleNumeric.headerLength N hash b initial ∧
      pushTouches N hash b middle = pushTouches N hash b initial ∧
      pushUpdates N hash b middle = pushUpdates N hash b initial := by
  have ha := header_member N hash a initial
  have hb := header_member N hash b initial
  have ne : ∀ x ∈ pushTouches N hash a initial, (b.word N hash) ≠ x.word N hash := by
    intro x inside same
    exact separate x inside b hb (run.word_inj
      (covered x (List.mem_append.mpr (Or.inl inside)))
      (covered b (List.mem_append.mpr (Or.inr hb))) same.symm)
  dsimp only [LifecycleNumeric.pushPrimitive] at executed
  split at executed
  next room =>
    cases executed
    have frame := header_two hash b initial _ _ ClearDemands.zero
      (lengthWord (LifecycleNumeric.headerLength N hash a initial + 1) room)
      (ne _ (element_member hash a initial room)) (ne a ha)
    dsimp only [twoWrites] at frame
    refine ⟨frame, ?_, ?_⟩
    · simp only [pushTouches, frame]
    · simp only [pushUpdates, frame]
  next full => cases executed

/-- Initial disjoint finite touches suffice for BOTH actual stages: the second
coverage follows from the derived header/access frame above. -/
theorem disjoint_sequence_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (a b : Solidity.Storage.Loc)
    (store : Store) (initial middle final : WordStore) (transport : Transport N hash locations store initial)
    (first : LifecycleNumeric.pushPrimitive N hash a initial = some middle)
    (second : LifecycleNumeric.pushPrimitive N hash b middle = some final)
    (covered : ∀ l ∈ pushTouches N hash a initial ++ pushTouches N hash b initial, l ∈ locations)
    (separate : ∀ x ∈ pushTouches N hash a initial, ∀ y ∈ pushTouches N hash b initial, x ≠ y) :
    Transport N hash locations
      ((pushUpdates N hash b middle).foldl (fun w op => Representation.write w op.1 op.2)
        ((pushUpdates N hash a initial).foldl (fun w op => Representation.write w op.1 op.2) store)) final := by
  apply push_sequence_transport run a b store initial middle final transport first second
  · intro l inside; exact covered l (List.mem_append.mpr (Or.inl inside))
  · intro l inside
    rw [(disjoint_frame run a b initial middle first covered separate).2.1] at inside
    exact covered l (List.mem_append.mpr (Or.inr inside))

private theorem pop_header_member (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (m : WordStore) :
    base ∈ popTouches N hash base m := by
  dsimp only [popTouches]
  split <;> exact List.mem_cons_self

private theorem pop_element_member {N : Nat} (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (m : WordStore)
    (live : 0 < LifecycleNumeric.headerLength N hash base m) :
    Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base m - 1) ∈ popTouches N hash base m := by
  rw [popTouches, if_pos live]
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- Disjoint actual push/pop including capacity/empty failure outcomes. -/
theorem push_pop {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (a b : Solidity.Storage.Loc) (m : WordStore)
    (covered : ∀ l ∈ pushTouches N hash a m ++ popTouches N hash b m, l ∈ locations)
    (separate : ∀ x ∈ pushTouches N hash a m, ∀ y ∈ popTouches N hash b m, x ≠ y) :
    (LifecycleNumeric.pushPrimitive N hash a m).bind (PrimitivePop.execute N hash b) =
      (PrimitivePop.execute N hash b m).bind (LifecycleNumeric.pushPrimitive N hash a) := by
  have ha := header_member N hash a m
  have hb := pop_header_member N hash b m
  have ne : ∀ x ∈ pushTouches N hash a m, ∀ y ∈ popTouches N hash b m, x.word N hash ≠ y.word N hash := by
    intro x insideX y insideY same
    exact separate x insideX y insideY (run.word_inj
      (covered x (List.mem_append.mpr (Or.inl insideX))) (covered y (List.mem_append.mpr (Or.inr insideY))) same)
  apply push_pop_physical hash a b m (ne a ha b hb)
  · intro room; exact Ne.symm (ne _ (element_member hash a m room) b hb)
  · intro live; exact ne a ha _ (pop_element_member hash b m live)
  · intro room live; exact ne _ (element_member hash a m room) _ (pop_element_member hash b m live)

theorem pop_pop {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (a b : Solidity.Storage.Loc) (m : WordStore)
    (covered : ∀ l ∈ popTouches N hash a m ++ popTouches N hash b m, l ∈ locations)
    (separate : ∀ x ∈ popTouches N hash a m, ∀ y ∈ popTouches N hash b m, x ≠ y) :
    (PrimitivePop.execute N hash a m).bind (PrimitivePop.execute N hash b) =
      (PrimitivePop.execute N hash b m).bind (PrimitivePop.execute N hash a) := by
  have ha := pop_header_member N hash a m
  have hb := pop_header_member N hash b m
  have ne : ∀ x ∈ popTouches N hash a m, ∀ y ∈ popTouches N hash b m, x.word N hash ≠ y.word N hash := by
    intro x insideX y insideY same
    exact separate x insideX y insideY (run.word_inj
      (covered x (List.mem_append.mpr (Or.inl insideX))) (covered y (List.mem_append.mpr (Or.inr insideY))) same)
  apply pop_pop_physical hash a b m (ne a ha b hb)
  · intro live; exact Ne.symm (ne _ (pop_element_member hash a m live) b hb)
  · intro live; exact ne a ha _ (pop_element_member hash b m live)
  · intro liveA liveB; exact ne _ (pop_element_member hash a m liveA) _ (pop_element_member hash b m liveB)

theorem pop_push {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (a b : Solidity.Storage.Loc) (m : WordStore)
    (covered : ∀ l ∈ popTouches N hash a m ++ pushTouches N hash b m, l ∈ locations)
    (separate : ∀ x ∈ popTouches N hash a m, ∀ y ∈ pushTouches N hash b m, x ≠ y) :
    (PrimitivePop.execute N hash a m).bind (LifecycleNumeric.pushPrimitive N hash b) =
      (LifecycleNumeric.pushPrimitive N hash b m).bind (PrimitivePop.execute N hash a) := by
  apply Eq.symm
  apply push_pop run b a m
  · intro l member
    rcases List.mem_append.mp member with left | right
    · exact covered l (List.mem_append.mpr (Or.inr left))
    · exact covered l (List.mem_append.mpr (Or.inl right))
  · intro x insideX y insideY
    exact Ne.symm (separate y insideY x insideX)

theorem pop_update_touched (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc)
    (m : WordStore) (op : Solidity.Storage.Loc × Semantics.Word) (member : op ∈ popUpdates N hash base m) :
    op.1 ∈ popTouches N hash base m := by
  dsimp only [popUpdates] at member
  split at member
  next live =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rw [popTouches, if_pos live]
    rcases member with rfl | rfl
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_self
  next empty => cases member

theorem pop_realized (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc)
    (initial final : WordStore) (executed : PrimitivePop.execute N hash base initial = some final) :
    final = (popUpdates N hash base initial).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial := by
  dsimp only [PrimitivePop.execute] at executed
  split at executed
  next live =>
    cases executed
    simp only [popUpdates, if_pos live, List.foldl_cons, List.foldl_nil]
  next empty => cases executed

/-- Generated pop writes transport under the same actual per-run conditions;
empty failure has no final-state or world-rollback conclusion. -/
theorem pop_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (base : Solidity.Storage.Loc)
    (store : Store) (initial final : WordStore) (transport : Transport N hash locations store initial)
    (executed : PrimitivePop.execute N hash base initial = some final)
    (covered : ∀ l ∈ popTouches N hash base initial, l ∈ locations) :
    Transport N hash locations
      ((popUpdates N hash base initial).foldl (fun w op => Representation.write w op.1 op.2) store) final := by
  rw [pop_realized N hash base initial final executed]
  apply transport_sequence run transport
  intro op member
  exact covered op.1 (pop_update_touched N hash base initial op member)

/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.pushTouches' does not depend on any axioms -/
#guard_msgs in #print axioms pushTouches
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.pushUpdates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pushUpdates
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.popTouches' does not depend on any axioms -/
#guard_msgs in #print axioms popTouches
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.popUpdates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms popUpdates
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.push_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms push_push
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.update_touched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms update_touched
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.push_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_realized
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.push_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_transport
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.push_sequence_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_sequence_transport
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.disjoint_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms disjoint_frame
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.disjoint_sequence_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms disjoint_sequence_transport
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.push_pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms push_pop
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.pop_pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pop_pop
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.pop_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pop_push
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.pop_update_touched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_update_touched
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.pop_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pop_realized
/-- info: 'Solidity.Backend.StorageOps.NumericCommutation.pop_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_transport

end Solidity.Backend.StorageOps.NumericCommutation
