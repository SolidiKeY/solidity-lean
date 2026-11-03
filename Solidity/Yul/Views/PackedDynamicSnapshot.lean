import Solidity.Yul.Views.PackedDynamicSeparation

namespace Solidity.Yul.Views

/-- Every computed supported dynamic root contributes ALL live indices from
its supplied raw header. No unsupported entry is silently skipped. -/
def ComputedStorage.unsignedSnapshot {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) : List (ScalarPath E.layout (E.lay a)) :=
  r.registrations ++ r.unsignedTrace.attach.flatMap (fun entry =>
    let h := r.unsignedHeader entry
    h.elements fixed a (m (h.registration a).slot))

theorem ComputedStorage.unsigned_root_member {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (c) (member : c ∈ r.registrations) :
    c ∈ r.unsignedSnapshot fixed m := List.mem_append_left _ member

theorem ComputedStorage.unsigned_element_member {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (entry : {entry // entry ∈ r.unsignedTrace}) (i : Nat)
    (bound : i < (m ((r.unsignedHeader entry).registration a).slot).val) :
    (r.unsignedHeader entry).element fixed a i ∈ r.unsignedSnapshot fixed m := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨entry,List.mem_attach _ _,((r.unsignedHeader entry).elements_member fixed a _ _).mpr ⟨i,bound,rfl⟩⟩

/-- The executable separation check examines computed physical fields. It is
not a caller-supplied adequacy/inverse law or a language admission condition.
None distinguishes unsupported/colliding canonical preparation from execution. -/
def ComputedStorage.unsignedSnapshotWriteback {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s : Source.Storage E.layout (E.lay a)) :=
  let cs := r.unsignedSnapshot fixed m
  if packedSeparationCheck cs then packedStoreWriteback cs m s else none

theorem ComputedStorage.unsigned_reencode {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.unsignedSnapshotWriteback fixed m s = some (out,residual)) :
    finiteEncode (r.unsignedSnapshot fixed m) out residual = some m := by
  unfold unsignedSnapshotWriteback at step
  dsimp only at step
  split at step
  · rename_i checked
    exact packedStoreWriteback_reencode _ _ _ _ _ ((packedSeparationCheck_iff _).mp checked) step
  · cases step

theorem ComputedStorage.unsigned_unselected {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.unsignedSnapshotWriteback fixed m s = some (out,residual)) (q : Source.SPath)
    (unselected : ∀ c ∈ r.unsignedSnapshot fixed m, q ≠ c.path) : out.cell q = s.cell q := by
  unfold unsignedSnapshotWriteback at step
  dsimp only at step
  split at step
  · exact packedStoreWriteback_other _ _ _ _ _ step q unselected
  · cases step

theorem ComputedStorage.unsigned_unchanged {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s : Source.Storage E.layout (E.lay a))
    (checked : packedSeparationCheck (r.unsignedSnapshot fixed m) = true)
    (view : finiteView (r.unsignedSnapshot fixed m) s m) :
    r.unsignedSnapshotWriteback fixed m s = some (s,packedMask (r.unsignedSnapshot fixed m) m) := by
  unfold unsignedSnapshotWriteback
  dsimp only
  rw [checked]
  exact packedStoreWriteback_unchanged _ _ _ _ view rfl

theorem ComputedStorage.unsigned_bank_agreement {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (c : ScalarPath E.layout (E.lay a))
    (member : c ∈ r.unsignedSnapshot fixed m) : E.transientRoot c.path = false := by
  rcases List.mem_append.mp member with original | dynamic
  · exact r.bank_agreement c original
  · obtain ⟨entry,_,inside⟩ := List.mem_flatMap.mp dynamic
    obtain ⟨i,_,same⟩ := ((r.unsignedHeader entry).elements_member fixed a _ c).mp inside
    subst c
    exact r.bank_agreement ((r.unsignedHeader entry).registration a) (r.unsignedHeader_member entry)

end Solidity.Yul.Views
