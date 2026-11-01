import Solidity.Yul.Views.DynamicInventoryWriteback

namespace Solidity.Yul.Views

/-- A trace entry's actual declaration and Word bound are proved by the SAME
successful packing. Only proof fields are extracted; the root/cursor remain the
computed data. There is no choice of coordinates or assumed view law. -/
def ComputedStorage.traceHeader {E ds d active a} (r : @ComputedStorage E ds d active a)
    (entry : {entry // entry ∈ r.headerTrace}) : DynamicHeader E entry.val.1 entry.val.2 where
  declared := by obtain ⟨h,_⟩ := r.header_present _ _ entry.property; exact h.declared
  bounded := by obtain ⟨h,_⟩ := r.header_present _ _ entry.property; exact h.bounded

/-- Every computed supported dynamic root contributes ALL live indices from
its supplied raw header. No unsupported entry is silently skipped. -/
def ComputedStorage.snapshotInventory {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) : List (ScalarPath E.layout (E.lay a)) :=
  r.registrations ++ r.headerTrace.attach.flatMap (fun entry =>
    let h := r.traceHeader entry
    h.elements fixed a (m (h.registration a).slot))

theorem ComputedStorage.snapshot_root_member {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (c) (member : c ∈ r.registrations) :
    c ∈ r.snapshotInventory fixed m := List.mem_append_left _ member

theorem ComputedStorage.snapshot_element_member {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (entry : {entry // entry ∈ r.headerTrace}) (i : Nat)
    (bound : i < (m ((r.traceHeader entry).registration a).slot).val) :
    (r.traceHeader entry).element fixed a i ∈ r.snapshotInventory fixed m := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨entry,List.mem_attach _ _,((r.traceHeader entry).elements_member fixed a _ _).mpr ⟨i,bound,rfl⟩⟩

/-- The executable separation check examines computed physical fields. It is
not a caller-supplied adequacy/inverse law or a language admission condition.
None distinguishes unsupported/colliding canonical preparation from execution. -/
def ComputedStorage.snapshotWriteback {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s : Source.Storage E.layout (E.lay a)) :=
  let cs := r.snapshotInventory fixed m
  if packedSeparationCheck cs then packedStoreWriteback cs m s else none

theorem ComputedStorage.snapshot_reencode {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.snapshotWriteback fixed m s = some (out,residual)) :
    finiteEncode (r.snapshotInventory fixed m) out residual = some m := by
  unfold snapshotWriteback at step
  dsimp only at step
  split at step
  · rename_i checked
    exact packedStoreWriteback_reencode _ _ _ _ _ ((packedSeparationCheck_iff _).mp checked) step
  · cases step

theorem ComputedStorage.snapshot_unselected {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.snapshotWriteback fixed m s = some (out,residual)) (q : Source.SPath)
    (unselected : ∀ c ∈ r.snapshotInventory fixed m, q ≠ c.path) : out.cell q = s.cell q := by
  unfold snapshotWriteback at step
  dsimp only at step
  split at step
  · exact packedStoreWriteback_other _ _ _ _ _ step q unselected
  · cases step

theorem ComputedStorage.snapshot_unchanged {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s : Source.Storage E.layout (E.lay a))
    (checked : packedSeparationCheck (r.snapshotInventory fixed m) = true)
    (view : finiteView (r.snapshotInventory fixed m) s m) :
    r.snapshotWriteback fixed m s = some (s,packedMask (r.snapshotInventory fixed m) m) := by
  unfold snapshotWriteback
  dsimp only
  rw [checked]
  exact packedStoreWriteback_unchanged _ _ _ _ view rfl

end Solidity.Yul.Views
