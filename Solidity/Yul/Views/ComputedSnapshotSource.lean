import Solidity.Yul.Views.ComputedDynamicSnapshot
import Solidity.Yul.Views.DynamicLengthCodec

namespace Solidity.Yul.Views

theorem ComputedStorage.traceHeader_member {E ds d active a} (r : @ComputedStorage E ds d active a)
    (entry : {entry // entry ∈ r.headerTrace}) : (r.traceHeader entry).registration a ∈ r.registrations := by
  obtain ⟨h,member⟩ := r.header_present _ _ entry.property
  rw [h.proof_irrel (r.traceHeader entry)] at member
  exact member

/-- Explicit EFFECTFUL canonical snapshot application through actual account
operations at the current frame's account. This is not pure unchanged-view
preparation, a raw Yul block semantics or a changing-ownership journal adapter.
Static refusal and ordinary operation administration remain Source.applyOp's. -/
def ComputedStorage.applySnapshot? {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (m : SlotView)
    (s : Source.EMState E Γ) : Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  let cs := r.snapshotInventory fixed m
  if packedSeparationCheck cs then
    (finiteAccountWrite? (T := E.lay) F.this cs m).map (fun op => (Source.applyOp F op).run s)
  else none

theorem actualApplyOp_run {E Γ} (F : Source.Fr) (op : Source.Op E.layout E.lay E.lay) (s : Source.EMState E Γ) :
    (Source.applyOp F op).run s = if F.static then (.error (.revert []),s)
      else (.ok (),(s.1,{s.2 with ex := s.2.ex.apply op})) := by
  unfold Source.applyOp
  cases F.static <;> rfl

theorem ComputedStorage.applySnapshot_static {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (m : SlotView)
    (s : Source.EMState E Γ) (result) (step : r.applySnapshot? F fixed m s = some result)
    (static : F.static = true) : result = (.error (.revert []),s) := by
  unfold applySnapshot? at step
  dsimp only at step
  split at step
  · obtain ⟨op,_,same⟩ := Option.map_eq_some_iff.mp step
    rw [actualApplyOp_run,static] at same
    exact same.symm
  · cases step

theorem ComputedStorage.applySnapshot_MemOK {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (m : SlotView)
    (s : Source.EMState E Γ) (result) (step : r.applySnapshot? F fixed m s = some result)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  unfold applySnapshot? at step
  dsimp only at step
  split at step
  · obtain ⟨op,_,same⟩ := Option.map_eq_some_iff.mp step
    rw [actualApplyOp_run] at same
    cases static : F.static
    · rw [static] at same
      cases same
      exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2.1,ok.2.2⟩
    · rw [static] at same
      cases same
      exact ok
  · cases step

/-- Actual successful source operation yields the full typed computed view.
No result/view law or manually supplied inventory is an input. -/
theorem ComputedStorage.applySnapshot_view {E ds d active Γ} (F : Source.Fr)
    (r : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed) (m : SlotView)
    (s out : Source.EMState E Γ) (step : r.applySnapshot? F fixed m s = some (.ok (),out))
    (static : F.static = false) :
    finiteView (r.snapshotInventory fixed m) (out.2.ex.world.accounts F.this).storage m := by
  unfold applySnapshot? at step
  dsimp only at step
  split at step
  · rename_i checked
    obtain ⟨op,prepared,same⟩ := Option.map_eq_some_iff.mp step
    rw [actualApplyOp_run,static] at same
    have state := congrArg Prod.snd same
    cases state
    exact finiteAccountWrite_view F.this _ m s.2.ex op ((packedSeparationCheck_iff _).mp checked) prepared
  · cases step

end Solidity.Yul.Views
