import Solidity.Yul.Views.ScalarOwnershipInventory

namespace Solidity.Yul.Views

/-- State-indexed checked preparation, not another source state. All fields
are actual computation/input equations. No final view/inverse/frame law fields. -/
structure ScalarOwnershipPlan {E ds d active Γ} (F : Source.Fr) (layout : @ComputedStorage E ds d active F.this)
    (fixed : Roadmap.Evm.Fixed) (written value : Roadmap.Word)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) where
  old : List (ScalarPath E.layout (E.lay F.this))
  oldComputed : layout.scalarFamilySourceInventory? F fixed s = some old
  raw : SlotView
  encoded : finiteEncode old (s.2.ex.world.accounts F.this).storage (fun q => r.cells (complementKey false F.this q)) = some raw
  oldChecked : packedSeparationCheck old = true
  nextChecked : packedSeparationCheck (layout.scalarFamilySnapshot fixed (saveSlot raw written value)) = true
  sourceOp : Source.Op E.layout E.lay E.lay
  prepared : finiteAccountWrite? F.this (layout.scalarFamilySnapshot fixed (saveSlot raw written value)) (saveSlot raw written value) = some sourceOp

def prepareScalarOwnership? {E ds d active Γ} (F : Source.Fr) (layout : @ComputedStorage E ds d active F.this)
    (fixed : Roadmap.Evm.Fixed) (written value : Roadmap.Word)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) :
    Option (ScalarOwnershipPlan F layout fixed written value s r) :=
  match oldComputed : layout.scalarFamilySourceInventory? F fixed s with
  | none => none
  | some old => match encoded : finiteEncode old (s.2.ex.world.accounts F.this).storage (fun q => r.cells (complementKey false F.this q)) with
    | none => none
    | some raw =>
      if oldChecked : packedSeparationCheck old = true then
        if nextChecked : packedSeparationCheck (layout.scalarFamilySnapshot fixed (saveSlot raw written value)) = true then
          match prepared : finiteAccountWrite? F.this (layout.scalarFamilySnapshot fixed (saveSlot raw written value)) (saveSlot raw written value) with
          | none => none
          | some op => some ⟨old,oldComputed,raw,encoded,oldChecked,nextChecked,op,prepared⟩
        else none
      else none

def ScalarOwnershipPlan.nextRaw {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) := saveSlot p.raw written value

def ScalarOwnershipPlan.next {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) := layout.scalarFamilySnapshot fixed p.nextRaw

def ScalarOwnershipPlan.updates {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) :=
  ownershipUpdates false F.this (ownershipSupport p.old p.next written) (packedMask p.next p.nextRaw)

def ScalarOwnershipPlan.step {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) :=
  let source := (Source.applyOp F p.sourceOp).run s
  (source,match source.1 with | .error _ => r | .ok _ => residualRun r p.updates)

theorem ScalarOwnershipPlan.old_agrees {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) : p.old = layout.scalarFamilySnapshot fixed p.raw := by
  have view := finiteEncode_view p.old _ _ p.raw ((packedSeparationCheck_iff _).mp p.oldChecked) p.encoded
  have roots : finiteView layout.registrations (s.2.ex.world.accounts F.this).storage p.raw := by
    intro c member
    exact view c (layout.scalarFamilySourceInventory_roots F fixed s p.old p.oldComputed c member)
  exact Option.some.inj (p.oldComputed.symm.trans (layout.scalarFamilySourceInventory_view F fixed s p.raw roots))

theorem ScalarOwnershipPlan.static {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = true) :
    p.step = ((.error (.revert []),s),r) := by
  unfold step
  rw [actualApplyOp_run,static]
  rfl

theorem ScalarOwnershipPlan.nonstatic {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    p.step = ((.ok (),(s.1,{s.2 with ex := s.2.ex.apply p.sourceOp})),residualRun r p.updates) := by
  unfold step
  rw [actualApplyOp_run,static]
  rfl

theorem ScalarOwnershipPlan.MemOK {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H p.step.1.2 := by
  cases static : F.static
  · rw [p.nonstatic static]
    exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2.1,ok.2.2⟩
  · rw [p.static static]
    exact ok

theorem ScalarOwnershipPlan.complement {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    (fun q => p.step.2.cells (complementKey false F.this q)) = packedMask p.next p.nextRaw := by
  rw [p.nonstatic static]
  exact ownership_transport_slice p.old p.next _ r false F.this p.raw p.encoded written value

theorem ScalarOwnershipPlan.view {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    finiteView p.next (p.step.1.2.2.ex.world.accounts F.this).storage p.nextRaw := by
  rw [p.nonstatic static]
  exact finiteAccountWrite_view F.this p.next p.nextRaw s.2.ex p.sourceOp ((packedSeparationCheck_iff _).mp p.nextChecked) p.prepared

theorem ScalarOwnershipPlan.reencode {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    finiteEncode p.next (p.step.1.2.2.ex.world.accounts F.this).storage
      (fun q => p.step.2.cells (complementKey false F.this q)) = some p.nextRaw := by
  rw [p.complement static]
  exact finiteEncode_fromComplement _ _ _ ((packedSeparationCheck_iff _).mp p.nextChecked) (p.view static)

end Solidity.Yul.Views
