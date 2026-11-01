import Solidity.Yul.Views.ComputedSnapshotSource

namespace Solidity.Yul.Views

/-- Complete actual readLen result derived from the checked declaration trace,
raw header, canonical snapshot application and real source bank metadata. -/
theorem ComputedStorage.applySnapshot_readLen {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (m : SlotView)
    (s out : Source.EMState E Γ) (step : r.applySnapshot? F fixed m s = some (.ok (),out))
    (static : F.static = false) (entry : {entry // entry ∈ r.headerTrace}) :
    (Source.readLen F ⟨entry.val.1,[]⟩).run out =
      (.ok (m ((r.traceHeader entry).registration F.this).slot).val,out) := by
  let h := r.traceHeader entry
  have member := r.traceHeader_member entry
  have view := r.applySnapshot_view F fixed m s out step static
  have headerView := view (h.registration F.this) (r.snapshot_root_member fixed m _ member)
  exact h.readLen F out _ (r.bank_agreement _ member) (h.view_length_cell F.this _ m headerView)

/-- Successful actual source application and the SAME supplied snapshot's
complement reencode the entire physical map, not only root projections. -/
theorem ComputedStorage.applySnapshot_reencode {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (m : SlotView)
    (s out : Source.EMState E Γ) (step : r.applySnapshot? F fixed m s = some (.ok (),out))
    (static : F.static = false) :
    finiteEncode (r.snapshotInventory fixed m) (out.2.ex.world.accounts F.this).storage
      (packedMask (r.snapshotInventory fixed m) m) = some m := by
  have view := r.applySnapshot_view F fixed m s out step static
  have checked : packedSeparationCheck (r.snapshotInventory fixed m) = true := by
    unfold ComputedStorage.applySnapshot? at step
    dsimp only at step
    split at step
    · assumption
    · cases step
  exact finiteEncode_fromComplement _ _ m ((packedSeparationCheck_iff _).mp checked) view

end Solidity.Yul.Views

namespace Solidity.Yul.Views

theorem ComputedStorage.snapshot_bank_agreement {E ds d active a} (r : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) (c : ScalarPath E.layout (E.lay a))
    (member : c ∈ r.snapshotInventory fixed m) : E.transientRoot c.path = false := by
  rcases List.mem_append.mp member with original | dynamic
  · exact r.bank_agreement c original
  · obtain ⟨entry,_,inside⟩ := List.mem_flatMap.mp dynamic
    obtain ⟨i,_,same⟩ := ((r.traceHeader entry).elements_member fixed a _ c).mp inside
    subst c
    exact r.bank_agreement ((r.traceHeader entry).registration a) (r.traceHeader_member entry)

theorem ComputedStorage.applySnapshot_readCell {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (m : SlotView)
    (s out : Source.EMState E Γ) (step : r.applySnapshot? F fixed m s = some (.ok (),out))
    (static : F.static = false) (c : ScalarPath E.layout (E.lay F.this))
    (member : c ∈ r.snapshotInventory fixed m) :
    ∃ v, (Source.readCell F c.path).run out = (.ok v,out) ∧ c.codec.encode v = c.field.findWord (m c.slot) := by
  have view := r.applySnapshot_view F fixed m s out step static
  obtain ⟨v,read,encoded⟩ := Option.map_eq_some_iff.mp (view c member)
  refine ⟨v,?_,encoded⟩
  unfold Source.readCell
  rw [Source.Hoare.run_bind,show (Source.EM.st (E := E) (Γ := Γ)).run out = (.ok out.2,out) from rfl]
  dsimp only
  rw [r.snapshot_bank_agreement fixed m c member]
  simp only [Bool.false_eq_true,if_false,read]
  rfl

end Solidity.Yul.Views
