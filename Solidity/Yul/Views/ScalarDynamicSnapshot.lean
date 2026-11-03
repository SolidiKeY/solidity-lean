import Solidity.Yul.Views.ScalarDynamicRegions

namespace Solidity.Yul.Views

/-- Every scalarFamilyTrace entry contributes ALL live indices from its supplied
raw header. This component does not claim integer/mapping/other live ownership;
those separate producer interfaces remain explicit composition obligations. -/
def ComputedStorage.scalarFamilySnapshot {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) : List (ScalarPath E.layout (E.lay a)) :=
  r.registrations ++ r.scalarFamilyTrace.attach.flatMap (fun entry =>
    let h := r.scalarFamilyHeader entry
    h.elements fixed a (m (h.registration a).slot))

theorem ComputedStorage.scalarFamily_root_member {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (c) (member : c ∈ r.registrations) :
    c ∈ r.scalarFamilySnapshot fixed m := List.mem_append_left _ member

theorem ComputedStorage.scalarFamily_element_member {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (entry : {entry // entry ∈ r.scalarFamilyTrace}) (i : Nat)
    (bound : i < (m ((r.scalarFamilyHeader entry).registration a).slot).val) :
    (r.scalarFamilyHeader entry).element fixed a i ∈ r.scalarFamilySnapshot fixed m := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨entry,List.mem_attach _ _,((r.scalarFamilyHeader entry).elements_member fixed a _ _).mpr ⟨i,bound,rfl⟩⟩

/-- The executable separation check examines computed physical fields. It is
not a caller-supplied adequacy/inverse law or a language admission condition.
None distinguishes unsupported/colliding canonical preparation from execution. -/
def ComputedStorage.scalarFamilySnapshotWriteback {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s : Source.Storage E.layout (E.lay a)) :=
  let cs := r.scalarFamilySnapshot fixed m
  if packedSeparationCheck cs then packedStoreWriteback cs m s else none

theorem ComputedStorage.scalarFamily_reencode {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.scalarFamilySnapshotWriteback fixed m s = some (out,residual)) :
    finiteEncode (r.scalarFamilySnapshot fixed m) out residual = some m := by
  unfold scalarFamilySnapshotWriteback at step
  dsimp only at step
  split at step
  · rename_i checked
    exact packedStoreWriteback_reencode _ _ _ _ _ ((packedSeparationCheck_iff _).mp checked) step
  · cases step

theorem ComputedStorage.scalarFamily_unselected {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.scalarFamilySnapshotWriteback fixed m s = some (out,residual)) (q : Source.SPath)
    (unselected : ∀ c ∈ r.scalarFamilySnapshot fixed m, q ≠ c.path) : out.cell q = s.cell q := by
  unfold scalarFamilySnapshotWriteback at step
  dsimp only at step
  split at step
  · exact packedStoreWriteback_other _ _ _ _ _ step q unselected
  · cases step

theorem ComputedStorage.scalarFamily_unchanged {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (s : Source.Storage E.layout (E.lay a))
    (checked : packedSeparationCheck (r.scalarFamilySnapshot fixed m) = true)
    (view : finiteView (r.scalarFamilySnapshot fixed m) s m) :
    r.scalarFamilySnapshotWriteback fixed m s = some (s,packedMask (r.scalarFamilySnapshot fixed m) m) := by
  unfold scalarFamilySnapshotWriteback
  dsimp only
  rw [checked]
  exact packedStoreWriteback_unchanged _ _ _ _ view rfl

theorem ComputedStorage.scalarFamily_bank_agreement {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (c : ScalarPath E.layout (E.lay a))
    (member : c ∈ r.scalarFamilySnapshot fixed m) : E.transientRoot c.path = false := by
  rcases List.mem_append.mp member with original | dynamic
  · exact r.bank_agreement c original
  · obtain ⟨entry,_,inside⟩ := List.mem_flatMap.mp dynamic
    obtain ⟨i,_,same⟩ := ((r.scalarFamilyHeader entry).elements_member fixed a _ c).mp inside
    subst c
    exact r.bank_agreement ((r.scalarFamilyHeader entry).registration a) (r.scalarFamilyHeader_member entry)

end Solidity.Yul.Views
