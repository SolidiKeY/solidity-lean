import Solidity.Yul.Views.IntOwnershipInventory
import Solidity.Yul.Views.ScalarOwnershipInventory

namespace Solidity.Yul.Views

/-- Append LIVE elements, never the two whole component snapshots: the actual
fixed registrations and length headers occur exactly once. -/
def ComputedStorage.primitiveIntegerLive {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) :=
  r.integerTrace.attach.flatMap (fun entry => let h := r.integerHeader entry; h.elements fixed a (m (h.registration a).slot))

def ComputedStorage.primitiveScalarLive {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) :=
  r.scalarFamilyTrace.attach.flatMap (fun entry => let h := r.scalarFamilyHeader entry; h.elements fixed a (m (h.registration a).slot))

def ComputedStorage.primitiveSnapshot {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) : List (ScalarPath E.layout (E.lay a)) :=
  r.registrations ++ (r.primitiveIntegerLive fixed m ++ r.primitiveScalarLive fixed m)

theorem ComputedStorage.primitive_member_iff {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (c) :
    c ∈ r.primitiveSnapshot fixed m ↔ c ∈ r.registrations ∨ c ∈ r.primitiveIntegerLive fixed m ∨ c ∈ r.primitiveScalarLive fixed m := by
  simp only [primitiveSnapshot,List.mem_append]

theorem ComputedStorage.primitive_root_member {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (c) (member : c ∈ r.registrations) : c ∈ r.primitiveSnapshot fixed m :=
  (r.primitive_member_iff fixed m c).mpr (Or.inl member)

theorem ComputedStorage.primitive_integer_subset {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (c) (member : c ∈ r.integerSnapshot fixed m) : c ∈ r.primitiveSnapshot fixed m := by
  rcases List.mem_append.mp member with root | live
  · exact r.primitive_root_member fixed m c root
  · exact (r.primitive_member_iff fixed m c).mpr (Or.inr (Or.inl live))

theorem ComputedStorage.primitive_scalar_subset {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (c) (member : c ∈ r.scalarFamilySnapshot fixed m) : c ∈ r.primitiveSnapshot fixed m := by
  rcases List.mem_append.mp member with root | live
  · exact r.primitive_root_member fixed m c root
  · exact (r.primitive_member_iff fixed m c).mpr (Or.inr (Or.inr live))

theorem ComputedStorage.primitive_bank_agreement {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (c) (member : c ∈ r.primitiveSnapshot fixed m) : E.transientRoot c.path = false := by
  rcases (r.primitive_member_iff fixed m c).mp member with root | integer | scalar
  · exact r.bank_agreement c root
  · exact r.integer_bank_agreement fixed m c (List.mem_append_right _ integer)
  · exact r.scalarFamily_bank_agreement fixed m c (List.mem_append_right _ scalar)

/-- Actual declarations rule out a root being in both selector families. -/
theorem primitive_dynamic_roots_ne {E ri rs t k ci cs}
    (h : IntDynamicHeader E ri t ci) (g : ScalarDynamicHeader E rs k cs) : ri ≠ rs := by
  intro same
  subst rs
  have types := h.declared.symm.trans g.declared
  cases k <;> cases types

/-- The successful executable check derives BOTH source-path uniqueness and
physical byte/slot separation over the actual combined output. -/
theorem ComputedStorage.primitive_checked_separated {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView)
    (checked : packedSeparationCheck (r.primitiveSnapshot fixed m) = true) : finiteSeparated (r.primitiveSnapshot fixed m) :=
  (packedSeparationCheck_iff _).mp checked

theorem ComputedStorage.primitive_checked_paths {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView)
    (checked : packedSeparationCheck (r.primitiveSnapshot fixed m) = true) :
    ((r.primitiveSnapshot fixed m).map ScalarPath.path).Nodup := by
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (fun h => h.1) (r.primitive_checked_separated fixed m checked)

def ComputedStorage.primitiveSnapshotWriteback {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s : Source.Storage E.layout (E.lay a)) :=
  if packedSeparationCheck (r.primitiveSnapshot fixed m) then packedStoreWriteback (r.primitiveSnapshot fixed m) m s else none

theorem ComputedStorage.primitive_reencode {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.primitiveSnapshotWriteback fixed m s = some (out,residual)) :
    finiteEncode (r.primitiveSnapshot fixed m) out residual = some m := by
  unfold primitiveSnapshotWriteback at step
  split at step
  · rename_i checked
    exact packedStoreWriteback_reencode _ _ _ _ _ ((packedSeparationCheck_iff _).mp checked) step
  · cases step

theorem ComputedStorage.primitive_unselected {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.primitiveSnapshotWriteback fixed m s = some (out,residual)) (q : Source.SPath)
    (unselected : ∀ c ∈ r.primitiveSnapshot fixed m, q ≠ c.path) : out.cell q = s.cell q := by
  unfold primitiveSnapshotWriteback at step
  split at step
  · exact packedStoreWriteback_other _ _ _ _ _ step q unselected
  · cases step

theorem ComputedStorage.primitive_unchanged {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s : Source.Storage E.layout (E.lay a))
    (checked : packedSeparationCheck (r.primitiveSnapshot fixed m) = true)
    (view : finiteView (r.primitiveSnapshot fixed m) s m) :
    r.primitiveSnapshotWriteback fixed m s = some (s,packedMask (r.primitiveSnapshot fixed m) m) := by
  unfold primitiveSnapshotWriteback
  rw [checked]
  exact packedStoreWriteback_unchanged _ _ _ _ view rfl


end Solidity.Yul.Views
