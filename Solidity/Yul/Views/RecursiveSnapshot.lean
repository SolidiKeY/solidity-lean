import Solidity.Yul.Views.RecursiveRootPaths
import Solidity.Yul.Views.MemberDynamicSnapshot

namespace Solidity.Yul.Views

/-- All enclosing fixed fields and headers occur ONCE. Both nested members and
ordinary primitive roots contribute live elements from their full source path. -/
def RecursiveComputedStorage.snapshot {E ds d active a} (r : @RecursiveComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) : List (ScalarPath E.layout (E.lay a)) :=
  r.registrations ++ r.headerTrace.attach.flatMap (fun entry =>
    let h := r.header entry
    h.elements fixed a (m (h.registration a).slot))

theorem RecursiveComputedStorage.snapshot_root_member {E ds d active a} (r : @RecursiveComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (c) (member : c ∈ r.registrations) : c ∈ r.snapshot fixed m :=
  List.mem_append_left _ member

theorem RecursiveComputedStorage.snapshot_live_member {E ds d active a} (r : @RecursiveComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (entry : {entry // entry ∈ r.headerTrace}) (c)
    (member : c ∈ (r.header entry).elements fixed a (m ((r.header entry).registration a).slot)) : c ∈ r.snapshot fixed m := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨entry,List.mem_attach _ _,member⟩

theorem RecursiveComputedStorage.snapshot_bank {E ds d active a} (r : @RecursiveComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (c) (member : c ∈ r.snapshot fixed m) : E.transientRoot c.path = false := by
  rcases List.mem_append.mp member with original | dynamic
  · exact r.bank_agreement c original
  · obtain ⟨entry,_,inside⟩ := List.mem_flatMap.mp dynamic
    have roots := (r.header entry).elements_root fixed a _ c inside
    unfold Source.Env.transientRoot
    rw [roots]
    exact r.bank_agreement _ (r.header_member entry)

def RecursiveComputedStorage.snapshotWriteback {E ds d active a} (r : @RecursiveComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s : Source.Storage E.layout (E.lay a)) :=
  if packedSeparationCheck (r.snapshot fixed m) then packedStoreWriteback (r.snapshot fixed m) m s else none

theorem RecursiveComputedStorage.snapshot_reencode {E ds d active a} (r : @RecursiveComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.snapshotWriteback fixed m s = some (out,residual)) :
    finiteEncode (r.snapshot fixed m) out residual = some m := by
  unfold snapshotWriteback at step
  split at step
  · exact packedStoreWriteback_reencode _ _ _ _ _ ((packedSeparationCheck_iff _).mp (by assumption)) step
  · cases step

theorem RecursiveComputedStorage.snapshot_unchanged {E ds d active a} (r : @RecursiveComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s : Source.Storage E.layout (E.lay a))
    (checked : packedSeparationCheck (r.snapshot fixed m) = true) (view : finiteView (r.snapshot fixed m) s m) :
    r.snapshotWriteback fixed m s = some (s,packedMask (r.snapshot fixed m) m) := by
  unfold snapshotWriteback
  rw [checked]
  exact packedStoreWriteback_unchanged _ _ _ _ view rfl

theorem RecursiveComputedStorage.snapshot_unselected {E ds d active a} (r : @RecursiveComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.snapshotWriteback fixed m s = some (out,residual)) (q : Source.SPath)
    (unselected : ∀ c ∈ r.snapshot fixed m, q ≠ c.path) : out.cell q = s.cell q := by
  unfold snapshotWriteback at step
  split at step
  · exact packedStoreWriteback_other _ _ _ _ _ step q unselected
  · cases step

end Solidity.Yul.Views
