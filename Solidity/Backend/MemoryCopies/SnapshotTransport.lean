import Solidity.Backend.MemoryCopies.SnapshotTransportInterface

/-! Observation invariance for the existing rank-bounded copy, proved using
its existing fields/array/fixed traversal and actual heap preservation. -/
namespace Solidity.Backend.MemoryCopies
open Semantics (tyRank fieldsRank structDef)

private theorem snapshot_fields_step {H H' : HTy} (extension : H <+: H') {k : Nat}
    (first : (T : Ty) → tyRank T < k → MVal H T → SVal T)
    (last : (T : Ty) → tyRank T < k → MVal H' T → SVal T)
    (preserved : ∀ (T : Ty) (bound : tyRank T < k) (value : MVal H T),
      last T bound (MVal.wk extension T value) = first T bound value) :
    (fields : List (Name × Ty)) → (bound : fieldsRank fields < k) → (values : MFields H fields) →
      MFields.copyBelow k last fields bound (MFields.wk extension fields values) = MFields.copyBelow k first fields bound values
  | [], _, _ => rfl
  | (_, T) :: fields, _, values => by
    simp only [MFields.copyBelow, MFields.wk]
    exact congr (congrArg SFields.cons (preserved T _ values.1))
      (snapshot_fields_step extension first last preserved fields _ values.2)

mutual
private theorem snapshot_copy_at {H H' : HTy} (extension : H <+: H') (before : Heap H) (after : Heap H')
    (kept : Heap.Keeps extension before after) {k : Nat}
    (first : (T : Ty) → tyRank T < k → MVal H T → SVal T)
    (last : (T : Ty) → tyRank T < k → MVal H' T → SVal T)
    (preserved : ∀ (T : Ty) (bound : tyRank T < k) (value : MVal H T),
      last T bound (MVal.wk extension T value) = first T bound value) :
    (T : Ty) → (bound : tyRank T < k + 1) → (value : MVal H T) →
      MVal.copyAt after k last T bound (MVal.wk extension T value) = MVal.copyAt before k first T bound value
  | .prim _, _, _ => rfl
  | .ref R, bound, reference => by
    simp only [MVal.copyAt, MVal.wk]
    exact snapshot_copy_ref_at extension before after kept first last preserved R bound reference

private theorem snapshot_copy_ref_at {H H' : HTy} (extension : H <+: H') (before : Heap H) (after : Heap H')
    (kept : Heap.Keeps extension before after) {k : Nat}
    (first : (T : Ty) → tyRank T < k → MVal H T → SVal T)
    (last : (T : Ty) → tyRank T < k → MVal H' T → SVal T)
    (preserved : ∀ (T : Ty) (bound : tyRank T < k) (value : MVal H T),
      last T bound (MVal.wk extension T value) = first T bound value) :
    (R : RefTy) → (bound : tyRank (.ref R) < k + 1) → (reference : HRef H R) →
      MVal.copyRefAt after k last R bound (reference.wk extension) = MVal.copyRefAt before k first R bound reference
  | .struct name, bound, reference => by
    simp only [MVal.copyRefAt, kept reference, MObj.wk]
    exact congrArg SVal.struct (snapshot_fields_step extension first last preserved (structDef name) _ (before.get reference))
  | .array E, bound, reference => by
    have members : ∀ value : MVal H E,
        MVal.copyAt after k last E (by simpa only [tyRank] using bound) (MVal.wk extension E value) =
          MVal.copyAt before k first E (by simpa only [tyRank] using bound) value :=
      fun value => snapshot_copy_at extension before after kept first last preserved E _ value
    simp only [MVal.copyRefAt]
    apply SVal.array_ofList_congr
    rw [kept reference]
    simp only [MObj.wk, List.map_map]
    exact congrArg (fun f => (before.get reference).val.map f) (funext members)
  | .fixed E n, bound, reference => by
    have members : ∀ value : MVal H E,
        MVal.copyAt after k last E (Nat.lt_of_succ_lt (by simpa only [tyRank] using bound)) (MVal.wk extension E value) =
          MVal.copyAt before k first E (Nat.lt_of_succ_lt (by simpa only [tyRank] using bound)) value :=
      fun value => snapshot_copy_at extension before after kept first last preserved E _ value
    simp only [MVal.copyRefAt, kept reference, MObj.wk]
    apply congrArg SVal.fixed
    apply SVec.eq_of_toList_eq
    simp only [SVec.toList_ofLen, List.map_map]
    exact congrArg (fun f => (before.get reference).val.map f) (funext members)
  | .mapping _ _, _, reference => (before.get reference : Empty).elim
end

theorem snapshot_copy_below {H H' : HTy} (extension : H <+: H') (before : Heap H) (after : Heap H')
    (kept : Heap.Keeps extension before after) :
    (fuel : Nat) → (T : Ty) → (bound : tyRank T < fuel) → (value : MVal H T) →
      MVal.copyBelow after fuel T bound (MVal.wk extension T value) = MVal.copyBelow before fuel T bound value
  | 0, _, bound, _ => absurd bound (Nat.not_lt_zero _)
  | fuel + 1, T, bound, value =>
    snapshot_copy_at extension before after kept _ _
      (fun T bound value => snapshot_copy_below extension before after kept fuel T bound value) T bound value

theorem kept_snapshot {H H' : HTy} (extension : H <+: H') (before : Heap H) (after : Heap H')
    (kept : Heap.Keeps extension before after) (T : Ty) (value : MVal H T) :
    MVal.copyMToSt after (MVal.wk extension T value) = MVal.copyMToSt before value :=
  snapshot_copy_below extension before after kept _ T _ value

theorem kept_index {H H' : HTy} (extension : H <+: H') (before : Heap H) (after : Heap H')
    (kept : Heap.Keeps extension before after) {A : RefTy} {E : Ty} (source : HRef H A)
    (shape : ArrTy A E) (index : PrimTy.uint.Denote) :
    after.index (source.wk extension) shape index = (before.index source shape index).map (MVal.wk extension E) := by
  simp only [Heap.index, kept source, MObj.elems_wk, List.getElem?_map]

theorem kept_selected_snapshot {H H' : HTy} (extension : H <+: H') (before : Heap H) (after : Heap H')
    (kept : Heap.Keeps extension before after) {A R : RefTy} (source : HRef H A)
    (shape : ArrTy A (.ref R)) (index : PrimTy.uint.Denote) (child : HRef H R)
    (selected : before.index source shape index = some child) :
    after.index (source.wk extension) shape index = some (child.wk extension) ∧
      MVal.copyMToSt after (T := .ref R) (child.wk extension) = MVal.copyMToSt before (T := .ref R) child := by
  rw [kept_index extension before after kept source shape index, selected]
  exact ⟨rfl, kept_snapshot extension before after kept (.ref R) child⟩

def snapshotTransport : SnapshotTransportCertificate := ⟨kept_snapshot, kept_index⟩

#print axioms snapshot_copy_below
#print axioms kept_snapshot
#print axioms kept_index
#print axioms kept_selected_snapshot
#print axioms snapshotTransport
end Solidity.Backend.MemoryCopies
